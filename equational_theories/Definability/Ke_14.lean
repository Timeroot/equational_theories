import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op X0 (M.op x x))
           have i₂ := b0e11 X0 (M.op X0 (M.op x x)) x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op X0 X0) (M.op X0 X0)
           have i₂ := b0e11 (M.op X0 X0) X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : x = (M.op x y) := by
        first
        | (have i₁ := b0e35 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e76 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e36 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e153 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e76 (σ x)
           grind)
        | exact superpose b0e76 b0e18
        | exact resolve b0e18 b0e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e155 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e153
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e153
        | exact resolve b0e153 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e153
      have b0e156 : False := by grind
      exact b0e156
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : x = (k x y) := by grind
        have b1e28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (M.op X0 (M.op x x))
             have i₂ := b1e12 X0 (M.op X0 (M.op x x)) x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : x = (M.op x y) := by
          first
          | (have i₁ := b1e28 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e28
          | exact resolve b1e28 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e38 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e38
        have b1e45 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e43
             have r₂ := b1e21
             grind)
          | exact resolve b1e43 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e47 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e45
          | exact resolve b1e45 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e47
          | exact resolve b1e47 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e47
        have b1e49 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e19
          | exact resolve b1e19 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e22
          | exact resolve b1e22 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e57 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e49
          | exact resolve b1e49 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e50
        have b1e58 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e57
          | exact resolve b1e57 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e57
        have b1e59 : False := by grind
        exact b1e59
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op X0 (M.op x x))
             have i₂ := b2e12 X0 (M.op X0 (M.op x x)) x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e293 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e50 x y
             grind)
          | exact superpose b2e50 b2e22
          | (have j1 := b2e50 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e50 x y
             grind)
          | exact resolve b2e22 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e304 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        clear b2e293
        have b2e318 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e304
             have r₂ := b2e21
             grind)
          | exact resolve b2e304 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e304
        have b2e327 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e318
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e318
          | exact resolve b2e318 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e318
        have b2e332 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e28 (σ y) (σ x)
             have i₂ := b2e327
             grind)
          | exact superpose b2e327 b2e28
          | exact resolve b2e28 b2e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e327
        have b2e334 : False := by grind
        exact b2e334
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e24
          | exact resolve b3e24 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e26 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e25
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : x = (k x y) := by
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
        have b3e50 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e56 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e50
        have b3e58 : y = (k x y) := by
          first
          | (have r₁ := b3e56
             have r₂ := b3e20
             grind)
          | exact resolve b3e56 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e60 : x = y := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e58
          | exact resolve b3e58 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e58
        have b3e61 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e19
          | exact resolve b3e19 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e21
          | exact resolve b3e21 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e61
             have i₂ := b3e64
             grind)
          | exact superpose b3e64 b3e61
          | exact resolve b3e61 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e64
        have b3e66 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e65
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e65
          | exact resolve b3e65 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e67 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e66
          | exact resolve b3e66 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60 b3e66
        have b3e68 : False := by grind
        exact b3e68
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (M.op X0 (M.op x x))
               have i₂ := b4e13 X0 (M.op X0 (M.op x x)) x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30 : x = (M.op x y) := by
            first
            | (have i₁ := b4e28 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e28
            | exact resolve b4e28 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e28 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e28
            | exact resolve b4e28 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e79 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e31
               grind)
            | exact superpose b4e31 b4e20
            | exact resolve b4e20 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e84 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e79
               have i₂ := b4e30
               grind)
            | exact superpose b4e30 b4e79
            | exact resolve b4e79 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e79
          have b4e85 : False := by grind
          exact b4e85
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b5e28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op X0 (M.op x x))
               have i₂ := b5e13 X0 (M.op X0 (M.op x x)) x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b5e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : x = (M.op x y) := by
            first
            | (have i₁ := b5e28 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e41 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e36
          have b5e43 : y = (k x y) := by
            first
            | (have r₁ := b5e41
               have r₂ := b5e21
               grind)
            | exact resolve b5e41 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e276 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e48 x y
               grind)
            | exact superpose b5e48 b5e24
            | (have j1 := b5e48 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e48 x y
               grind)
            | exact resolve b5e24 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e287 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b5e276
          have b5e301 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e287
               have r₂ := b5e23
               grind)
            | exact resolve b5e287 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e287
          have b5e310 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e301
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e301
            | exact resolve b5e301 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e301
          have b5e315 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e28 (σ y) (σ x)
               have i₂ := b5e310
               grind)
            | exact superpose b5e310 b5e28
            | exact resolve b5e28 b5e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e310
          have b5e381 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29 (σ y) X0
               have i₂ := b5e315
               grind)
            | exact superpose b5e315 b5e29
            | exact resolve b5e29 b5e315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29 b5e315
          have b5e427 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e381 (σ x)
               grind)
            | exact superpose b5e381 b5e20
            | exact resolve b5e20 b5e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e381
          have b5e445 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e427
               have i₂ := b5e30
               grind)
            | exact superpose b5e30 b5e427
            | exact resolve b5e427 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e427
          have b5e446 : False := by grind
          exact b5e446
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
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
        have b6e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (M.op X0 (M.op x x))
             have i₂ := b6e12 X0 (M.op X0 (M.op x x)) x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e86 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e73
             have r₂ := b6e20
             grind)
          | exact resolve b6e73 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e90 : x = (M.op x y) := by
          first
          | (have r₁ := b6e86
             have r₂ := b6e21
             grind)
          | exact resolve b6e86 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e93 : y = (M.op y x) := by
          first
          | (have i₁ := b6e41 y x
             have i₂ := b6e90
             grind)
          | exact superpose b6e90 b6e41
          | exact resolve b6e41 b6e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e90
        have b6e95 : False := by grind
        exact b6e95
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b7e28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (M.op X0 (M.op x x))
               have i₂ := b7e13 X0 (M.op X0 (M.op x x)) x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b7e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e41 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e36
          have b7e43 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e23
               grind)
            | exact resolve b7e41 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e43
            | exact resolve b7e43 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e73 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e14
            | exact resolve b7e14 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e74 : y = (k x y) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e73
            | exact resolve b7e73 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e87 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e88 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e87
               have r₂ := b7e21
               grind)
            | exact resolve b7e87 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e90 : y = (M.op x y) := by
            first
            | (have r₁ := b7e88
               have r₂ := b7e22
               grind)
            | exact resolve b7e88 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e102 : y = (M.op y y) := by
            first
            | (have i₁ := b7e28 y x
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e28
            | exact resolve b7e28 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e114 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e29 y X0
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e29
            | exact resolve b7e29 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e102
          have b7e120 : x = y := by
            first
            | (have i₁ := b7e90
               have i₂ := b7e114 x
               grind)
            | exact superpose b7e114 b7e90
            | exact resolve b7e90 b7e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e158 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e120
               grind)
            | exact superpose b7e120 b7e22
            | exact resolve b7e22 b7e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e165 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e114 X0
               have i₂ := b7e120
               grind)
            | exact superpose b7e120 b7e114
            | exact resolve b7e114 b7e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e114 b7e120
          have b7e166 : False := by grind
          exact b7e166
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b8e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b8e272 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e53 x y
               grind)
            | exact superpose b8e53 b8e24
            | (have j1 := b8e53 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e53 x y
               grind)
            | exact resolve b8e24 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e283 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b8e272
          have b8e297 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e283
               have r₂ := b8e23
               grind)
            | exact resolve b8e283 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e283
          have b8e306 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e297
               grind)
            | exact superpose b8e297 b8e20
            | exact resolve b8e20 b8e297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e297
          have b8e343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e306
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e306
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e306 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e306
          have b8e344 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e343
          have b8e348 : y = (M.op y x) := by
            first
            | (have r₁ := b8e344
               have r₂ := b8e21
               grind)
            | exact resolve b8e344 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e344
          have b8e350 : False := by grind
          exact b8e350

/-- `Equation4364`: `x ◇ (y ◇ z) = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation4364 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4364 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4364.models_iff G M).mp hM
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
      have b0e63 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e66 : False := by grind
      exact b0e66
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
          have b5e56 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e60 : x = y ∨ x = (k x y) := by grind
          clear b5e56
          have b5e61 : x = (k x y) := by
            first
            | (have r₁ := b5e60
               have r₂ := b5e21
               grind)
            | exact resolve b5e60 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e1093 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e64 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e119554 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1093 x y
               have i₂ := b5e61
               grind)
            | exact superpose b5e61 b5e1093
            | (have j0 := b5e1093 x y
               grind)
            | exact resolve b5e1093 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61 b5e1093
          have b5e119557 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e119554
          have b5e119559 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e119557
               have r₂ := b5e24
               grind)
            | exact resolve b5e119557 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e119557
          have b5e119561 : False := by grind
          exact b5e119561
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
          have b7e49 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e64 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e54
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e54 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e65 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e26
               grind)
            | exact resolve b7e64 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e64
          have b7e66 : x = y := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e22
               grind)
            | exact resolve b7e65 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : False := by grind
          exact b7e67
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
          have b8e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e928 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e951 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e928
               have r₂ := b8e24
               grind)
            | exact resolve b8e928 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e928
          have b8e957 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e951
               have r₂ := b8e23
               grind)
            | exact resolve b8e951 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e951
          have b8e960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e957
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e957
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e957
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e957
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e957 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e957
          have b8e961 : x = (M.op x y) ∨ x = y := by grind
          clear b8e960
          have b8e962 : x = y := by
            first
            | (have r₁ := b8e961
               have r₂ := b8e22
               grind)
            | exact resolve b8e961 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e961
          have b8e963 : False := by grind
          exact b8e963

/-- `Equation4384`: `x ◇ (x ◇ x) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyy_x_pxy_Equation4384 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4384 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4384.models_iff G M).mp hM
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X2) := by
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
        have b1e37 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
        have b1e38 : ∀ X0 : G, (M.op x (M.op x x)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x y X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 X1
             have i₂ := b1e38 X0
             grind)
          | (have i₁ := b1e38 X0
             have i₂ := b1e38 (M.op x x)
             grind)
          | exact superpose b1e38 b1e38
          | exact resolve b1e38 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e117 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e20
             have i₂ := b1e42 y X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e42 X0 y
             grind)
          | exact superpose b1e42 b1e20
          | exact resolve b1e20 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e126 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e21
          | exact resolve b1e21 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e150 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e117 X0
             grind)
          | exact superpose b1e117 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x X0
             have r₂ := b1e117 X0
             grind)
          | exact resolve b1e15 b1e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e152 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e150 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e150
        have b1e380 : (σ y) = (k x (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e152 (σ x)
             grind)
          | exact superpose b1e152 b1e22
          | exact resolve b1e22 b1e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e381 : (σ x) ≠ (k x (σ y)) := by
          first
          | (have i₁ := b1e126 (σ y)
             have i₂ := b1e152 (σ y)
             grind)
          | exact superpose b1e152 b1e126
          | exact resolve b1e126 b1e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126
        have b1e1412 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e75 x x
             grind)
          | exact superpose b1e75 b1e22
          | (have j1 := b1e75 x x
             grind)
          | exact resolve b1e22 b1e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e1485 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e1412
        have b1e1535 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e1485
             have i₂ := b1e152 x
             grind)
          | exact superpose b1e152 b1e1485
          | exact resolve b1e1485 b1e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e152 b1e1485
        have b1e1593 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e1535
             have i₂ := b1e117 x
             grind)
          | exact superpose b1e117 b1e1535
          | exact resolve b1e1535 b1e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e117 b1e1535
        have b1e1623 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1593
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1593
          | exact resolve b1e1593 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1593
        have b1e1624 : (σ x) = (σ y) := by grind
        clear b1e1623
        have b1e1686 : (σ x) ≠ (k x (σ x)) := by
          first
          | (have i₁ := b1e381
             have i₂ := b1e1624
             grind)
          | exact superpose b1e1624 b1e381
          | exact resolve b1e381 b1e1624
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e381
        have b1e1706 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e1686
             have i₂ := b1e380
             grind)
          | exact superpose b1e380 b1e1686
          | exact resolve b1e1686 b1e380
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e380 b1e1686
        have b1e1711 : False := by grind
        exact b1e1711
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
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
        have b2e34 : ∀ X0 : G, (M.op x (M.op x x)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e12 x y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 X1
             have i₂ := b2e34 X0
             grind)
          | (have i₁ := b2e34 X0
             have i₂ := b2e34 (M.op x x)
             grind)
          | exact superpose b2e34 b2e34
          | exact resolve b2e34 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e76 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e20
             have i₂ := b2e40 y X0
             grind)
          | (have i₁ := b2e20
             have i₂ := b2e40 X0 y
             grind)
          | exact superpose b2e40 b2e20
          | exact resolve b2e20 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e104 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e76 X0
             grind)
          | exact superpose b2e76 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x X0
             have r₂ := b2e76 X0
             grind)
          | exact resolve b2e15 b2e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e106 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e104 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104
        have b2e123 : ∀ X0 X1 : G, (M.op X0 (k x X0)) = (M.op (k x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X0 x
             have i₂ := b2e106 X0
             grind)
          | exact superpose b2e106 b2e12
          | exact resolve b2e12 b2e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1645 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e84 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e1647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e1645 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1645
        have b2e1668 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e1647 X0
             have i₂ := b2e106 (σ X0)
             grind)
          | exact superpose b2e106 b2e1647
          | (have j0 := b2e1647 X0
             grind)
          | exact resolve b2e1647 b2e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1647
        have b2e3869 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k x (σ x)) := by
          first
          | (have i₁ := b2e1668 x
             have i₂ := b2e106 x
             grind)
          | exact superpose b2e106 b2e1668
          | (have j0 := b2e1668 x
             grind)
          | exact resolve b2e1668 b2e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1668
        have b2e3877 : (σ x) ≠ (σ x) ∨ (σ x) = (k x (σ x)) := by
          first
          | (have i₁ := b2e3869
             have i₂ := b2e76 x
             grind)
          | exact superpose b2e76 b2e3869
          | exact resolve b2e3869 b2e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76 b2e3869
        have b2e3878 : (σ x) = (k x (σ x)) := by grind
        clear b2e3877
        have b2e3907 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e123 (σ x) x
             have i₂ := b2e3878
             grind)
          | exact superpose b2e3878 b2e123
          | exact resolve b2e123 b2e3878
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123
        have b2e3919 : ∀ X0 : G, (M.op (σ x) X0) = (k x (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e3907 X0
             have i₂ := b2e106 (σ x)
             grind)
          | exact superpose b2e106 b2e3907
          | exact resolve b2e3907 b2e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106 b2e3907
        have b2e3921 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e3919 X0
             have i₂ := b2e3878
             grind)
          | exact superpose b2e3878 b2e3919
          | exact resolve b2e3919 b2e3878
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3878 b2e3919
        have b2e4133 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e3921 (σ y)
             grind)
          | exact superpose b2e3921 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e3921 (σ y)
             grind)
          | exact resolve b2e21 b2e3921
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3921
        have b2e4183 : False := by grind
        exact b2e4183
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
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
        have b3e32 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e81 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b3e219 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X1
             have i₂ := b3e32 X0
             grind)
          | (have i₁ := b3e32 X0
             have i₂ := b3e32 (M.op (σ x) (σ x))
             grind)
          | exact superpose b3e32 b3e32
          | exact resolve b3e32 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e263 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e22
             have i₂ := b3e219 (σ y) X0
             grind)
          | (have i₁ := b3e22
             have i₂ := b3e219 X0 (σ y)
             grind)
          | exact superpose b3e219 b3e22
          | exact resolve b3e22 b3e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e219
        have b3e414 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e263 X0
             grind)
          | exact superpose b3e263 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) X0
             have r₂ := b3e263 X0
             grind)
          | exact resolve b3e15 b3e263
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e416 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e414 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e414
        have b3e458 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e81 x X0
             have i₂ := b3e416 X0
             grind)
          | exact superpose b3e416 b3e81
          | exact resolve b3e81 b3e416
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e416
        have b3e679 : (τ (σ x)) = (k x (τ (σ x))) := by
          first
          | (have i₁ := b3e458 (σ x)
             have i₂ := b3e263 (σ x)
             grind)
          | exact superpose b3e263 b3e458
          | exact resolve b3e458 b3e263
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e263 b3e458
        have b3e690 : x = (k x x) := by
          first
          | (have i₁ := b3e679
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e679
          | exact resolve b3e679 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e679
        have b3e889 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e690
             grind)
          | exact superpose b3e690 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e690
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e690
        have b3e890 : x = (M.op x x) := by grind
        clear b3e889
        have b3e898 : x = y := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e890
             grind)
          | exact superpose b3e890 b3e21
          | exact resolve b3e21 b3e890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1121 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e898
             grind)
          | exact superpose b3e898 b3e20
          | exact resolve b3e20 b3e898
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e898
        have b3e1133 : False := by grind
        exact b3e1133
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
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
          have b4e38 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
          have b4e39 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
          have b4e46 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X0 (M.op X0 X0)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b4e16 (M.op X0 (M.op X0 X0)) X2
               have r₂ := b4e13 X0 (M.op X0 X0) X2
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e39 X0
               grind)
            | exact superpose b4e39 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | exact resolve b4e16 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e46 X0 X1 X2
               have i₂ := b4e13 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e13 b4e46
            | (have j0 := b4e46 X0 X1 X2
               grind)
            | exact resolve b4e46 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e75 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X0 X2
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e90 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X1
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e38
            | exact resolve b4e38 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e93 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e20
            | exact resolve b4e20 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e199 : ∀ X0 X1 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op X1 X1) = (k (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ y) X1
               have i₂ := b4e90 X1 X0
               grind)
            | (have i₁ := b4e16 (σ y) X1
               have i₂ := b4e90 X0 X1
               grind)
            | exact superpose b4e90 b4e16
            | (have j0 := b4e16 (σ y) X0
               grind)
            | exact resolve b4e16 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e666 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e52 X0 X0 X2
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e52 X0 X1 X2
               have i₂ := b4e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b4e18 b4e52
            | (have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e52 X1 X1 (M.op X1 X1)
               have r₂ := b4e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b4e52 (M.op X0 X0) X1 X2
               have r₂ := b4e18 X0 (M.op (M.op (M.op X0 X0) X1) X2)
               grind)
            | exact resolve b4e52 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e693 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e666 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e666
          have b4e859 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e18 X0 X2
               have i₂ := b4e75 X0 X0 X1
               grind)
            | (have i₁ := b4e18 X2 X1
               have i₂ := b4e75 X2 X1 X2
               grind)
            | exact superpose b4e75 b4e18
            | (have j0 := b4e18 X0 X0
               have j1 := b4e75 X2 X0 X2
               grind)
            | exact resolve b4e18 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e969 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e859 X0 X0 X0
               have j1 := b4e693 X0 X0 X2
               grind)
            | (have r₁ := b4e859 X0 X2 X1
               have r₂ := b4e693 X0 X1 X2
               grind)
            | (have r₁ := b4e859 X0 X1 (M.op X0 X2)
               have r₂ := b4e693 X0 (M.op X0 X1) X2
               grind)
            | (have r₁ := b4e859 X0 X1 X2
               have r₂ := b4e693 X0 (k X0 X2) X2
               grind)
            | exact resolve b4e859 b4e693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e693 b4e859
          have b4e990 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e969 X0 X1 X2
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e969 X0 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e969 X0 X1 (M.op (M.op X0 X1) X1)
               have r₂ := b4e16 (M.op X0 X1) X1
               grind)
            | (have r₁ := b4e969 X1 X1 X2
               have r₂ := b4e16 X1 X1
               grind)
            | exact resolve b4e969 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e969
          have b4e11629 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e990 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e990
          have b4e11630 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e11629 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11629
          have b4e12026 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e90 X0 x
               have i₂ := b4e11630 (σ y) x
               grind)
            | exact superpose b4e11630 b4e90
            | (have j1 := b4e11630 (σ y) X0
               grind)
            | exact resolve b4e90 b4e11630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e12053 : y = (M.op x y) ∨ (M.op y y) = (k y y) := by
            first
            | (have i₁ := b4e39 x
               have i₂ := b4e11630 y x
               grind)
            | exact superpose b4e11630 b4e39
            | (have j1 := b4e11630 y x
               grind)
            | exact resolve b4e39 b4e11630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11630
          have b4e12112 : (M.op y y) = (k y y) := by
            first
            | (have j1 := b4e50 y
               grind)
            | (have r₁ := b4e12053
               have r₂ := b4e50 x
               grind)
            | exact resolve b4e12053 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50 b4e12053
          have b4e12133 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have j1 := b4e199 x (σ y)
               grind)
            | (have r₁ := b4e12026 x
               have r₂ := b4e199 x x
               grind)
            | exact resolve b4e12026 b4e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e199 b4e12026
          have b4e12184 : (M.op x y) = (k y y) := by
            first
            | (have i₁ := b4e12112
               have i₂ := b4e39 y
               grind)
            | exact superpose b4e39 b4e12112
            | exact resolve b4e12112 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e12112
          have b4e12204 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e12133
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e12133
            | exact resolve b4e12133 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12133
          have b4e12252 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e12204
               have i₂ := b4e12184
               grind)
            | exact superpose b4e12184 b4e12204
            | exact resolve b4e12204 b4e12184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12184 b4e12204
          have b4e12281 : False := by grind
          exact b4e12281
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
          have b5e50 : x = (k x y) ∨ x = (M.op x y) := by grind
          have b5e55 : x = (k x y) := by
            first
            | (have r₁ := b5e50
               have r₂ := b5e21
               grind)
            | exact resolve b5e50 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b5e806 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e69 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e807 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e806
               have r₂ := b5e23
               grind)
            | exact resolve b5e806 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e806
          have b5e808 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e807
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e807
            | exact resolve b5e807 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e807
          have b5e809 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e808
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e808
            | exact resolve b5e808 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e808
          have b5e810 : False := by grind
          exact b5e810
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
        have b6e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b6e30 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) X0) := by
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
        have b6e51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e26 X1 X0
             grind)
          | exact superpose b6e26 b6e13
          | exact resolve b6e13 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e142 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e30 X1
             have i₂ := b6e30 X0
             grind)
          | (have i₁ := b6e30 X0
             have i₂ := b6e30 (M.op (σ x) (σ x))
             grind)
          | exact superpose b6e30 b6e30
          | exact resolve b6e30 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e181 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e22
             have i₂ := b6e142 (σ y) X0
             grind)
          | (have i₁ := b6e22
             have i₂ := b6e142 X0 (σ y)
             grind)
          | exact superpose b6e142 b6e22
          | exact resolve b6e22 b6e142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142
        have b6e248 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e181 X0
             grind)
          | exact superpose b6e181 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) X0
             have r₂ := b6e181 X0
             grind)
          | exact resolve b6e15 b6e181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e250 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e248 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e248
        have b6e389 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e51 x X0
             have i₂ := b6e250 X0
             grind)
          | exact superpose b6e250 b6e51
          | exact resolve b6e51 b6e250
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e250
        have b6e408 : (τ (σ x)) = (k x (τ (σ x))) := by
          first
          | (have i₁ := b6e389 (σ x)
             have i₂ := b6e181 (σ x)
             grind)
          | exact superpose b6e181 b6e389
          | exact resolve b6e389 b6e181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e181 b6e389
        have b6e424 : x = (k x x) := by
          first
          | (have i₁ := b6e408
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e408
          | exact resolve b6e408 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e408
        have b6e488 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e424
             grind)
          | exact superpose b6e424 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e424
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e424
        have b6e489 : x = (M.op x x) := by grind
        clear b6e488
        have b6e557 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e12 x x x
             have i₂ := b6e489
             grind)
          | exact superpose b6e489 b6e12
          | exact resolve b6e12 b6e489
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e572 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e557 X0
             have i₂ := b6e489
             grind)
          | exact superpose b6e489 b6e557
          | exact resolve b6e557 b6e489
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e489 b6e557
        have b6e743 : x ≠ x := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e572 y
             grind)
          | exact superpose b6e572 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e572 y
             grind)
          | exact resolve b6e20 b6e572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e572
        have b6e759 : False := by grind
        exact b6e759
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
          have b7e69 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          have b7e76 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e23
               grind)
            | exact resolve b7e69 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e77 : (σ x) = (σ (k x y)) := by
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
          have b7e80 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e14
            | exact resolve b7e14 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e81 : x = (k x y) := by
            first
            | (have i₁ := b7e80
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e80
            | exact resolve b7e80 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e104 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e81
               grind)
            | exact superpose b7e81 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e105 : x = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b7e104
          have b7e107 : y = (M.op x x) := by
            first
            | (have r₁ := b7e105
               have r₂ := b7e21
               grind)
            | exact resolve b7e105 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e109 : False := by grind
          exact b7e109
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
          have b8e90 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b8e840 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e90 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e841 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e840
               have r₂ := b8e23
               grind)
            | exact resolve b8e840 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e840
          have b8e842 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e841
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e841
            | exact resolve b8e841 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e841
          have b8e845 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e842
               grind)
            | exact superpose b8e842 b8e20
            | exact resolve b8e20 b8e842
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e842
          have b8e1263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e845
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e845
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e845 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e845
          have b8e1264 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e1263
          have b8e1267 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1264
               have r₂ := b8e22
               grind)
            | exact resolve b8e1264 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1264
          have b8e1270 : False := by grind
          exact b8e1270

/-- `Equation4385`: `x ◇ (x ◇ x) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation4385 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4385 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4385.models_iff G M).mp hM
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
    · rcases eq_or_ne (y) (x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          grind
        have b0e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          grind
        clear b0e30
        have b0e62 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
        clear b0e31
        have b0e65 : False := by grind
        exact b0e65
      · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
        · have b1e21 : x = y := by grind
          have b1e23 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e30 : False := by grind
          exact b1e30
        · have b2e21 : x = y := by grind
          have b2e23 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e30 : False := by grind
          exact b2e30
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b3e21 : x = y := by grind
          have b3e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e30 : False := by grind
          exact b3e30
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b4e22 : x = y := by grind
            have b4e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e33 : False := by grind
            exact b4e33
          · have b5e22 : x = y := by grind
            have b5e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e33 : False := by grind
            exact b5e33
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b6e21 : x = y := by grind
          have b6e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e30 : False := by grind
          exact b6e30
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b7e22 : x = y := by grind
            have b7e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e33 : False := by grind
            exact b7e33
          · have b8e22 : x = y := by grind
            have b8e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e33 : False := by grind
            exact b8e33
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b9e21 : x ≠ y := by grind
          have b9e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e30 : False := by grind
          exact b9e30
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e24 : (σ x) = (σ y) := by grind
            have b10e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 y
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e15
              | exact resolve b10e15 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e31 : x = y := by
              first
              | (have i₁ := b10e30
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e30
              | exact resolve b10e30 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e30
            have b10e32 : False := by grind
            exact b10e32
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e24 : (σ x) = (σ y) := by grind
            have b11e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e29 : y = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 y
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e15
              | exact resolve b11e15 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e30 : x = y := by
              first
              | (have i₁ := b11e29
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e29
              | exact resolve b11e29 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e29
            have b11e31 : False := by grind
            exact b11e31
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b12e24 : (σ x) ≠ (σ y) := by grind
            have b12e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e33 : False := by grind
            exact b12e33
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                grind
              have b13e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b13e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b13e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : y = (M.op y x) := by grind
              have b13e25 : (σ x) ≠ (σ y) := by grind
              have b13e27 : x ≠ y := by grind
              have b13e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : (σ x) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e22
                | exact resolve b13e22 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 (τ X0) X1
                   have i₂ := b13e17 X0
                   grind)
                | exact superpose b13e17 b13e21
                | exact resolve b13e21 b13e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b13e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b13e34
              have b13e44 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e15 X1 X2
                   have i₂ := b13e15 X1 X0
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e45 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
                intro X0
                first
                | (have i₁ := b13e15 X0 (M.op x X0)
                   have i₂ := b13e15 X0 x
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e47 : (M.op x y) = (M.op y (M.op y y)) := by
                first
                | (have i₁ := b13e15 y x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e50 : x = (M.op y (M.op y y)) := by
                first
                | (have i₁ := b13e47
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e47
                | exact resolve b13e47 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e47
              have b13e54 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b13e19 X0 (M.op X1 X0)
                   have i₂ := b13e15 X0 X1
                   grind)
                | exact superpose b13e15 b13e19
                | (have j0 := b13e19 (M.op X1 X0) X0
                   grind)
                | exact resolve b13e19 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e56 : x ≠ x ∨ x = y ∨ y = (k y x) := by
                first
                | (have i₁ := b13e19 y x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e19
                | (have j0 := b13e19 x y
                   grind)
                | (have r₁ := b13e19 y x
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e19 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e60 : x = y ∨ y = (k y x) := by grind
              clear b13e56
              have b13e63 : y = (k y x) := by
                first
                | (have r₁ := b13e60
                   have r₂ := b13e27
                   grind)
                | exact resolve b13e60 b13e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e60
              have b13e68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
              have b13e69 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b13e31 X1 X0
                   have i₂ := b13e20 (τ X1) X0
                   grind)
                | exact superpose b13e20 b13e31
                | (have j1 := b13e20 (τ X1) X0
                   grind)
                | exact resolve b13e31 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e31
              have b13e89 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 (σ X0) X1
                   have i₂ := b13e35 X0
                   grind)
                | exact superpose b13e35 b13e15
                | exact resolve b13e15 b13e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e223 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b13e54 (σ X0) (σ X0)
                   have i₂ := b13e35 X0
                   grind)
                | exact superpose b13e35 b13e54
                | exact resolve b13e54 b13e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e54
              have b13e226 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e223 X0
                   have i₂ := b13e21 X0 (M.op X0 X0)
                   grind)
                | exact superpose b13e21 b13e223
                | (have j0 := b13e223 X0
                   grind)
                | exact resolve b13e223 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e223
              have b13e258 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X0)) = (M.op (M.op X2 (σ X0)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e44 (σ X1) (σ X0) X2
                   have i₂ := b13e68 X1 X0
                   grind)
                | exact superpose b13e68 b13e44
                | (have j1 := b13e68 X1 X0
                   grind)
                | exact resolve b13e44 b13e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e44 b13e68
              have b13e1318 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                first
                | (have i₁ := b13e69 X0 (σ X0)
                   have i₂ := b13e16 X0
                   grind)
                | exact superpose b13e16 b13e69
                | exact resolve b13e69 b13e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e69
              have b13e1370 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                first
                | (have i₁ := b13e1318 X0 X1
                   have i₂ := b13e21 X0 X1
                   grind)
                | exact superpose b13e21 b13e1318
                | (have j0 := b13e1318 X0 X1
                   grind)
                | exact resolve b13e1318 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1318
              have b13e1970 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have i₁ := b13e258 y x X0
                   have i₂ := b13e63
                   grind)
                | exact superpose b13e63 b13e258
                | (have j0 := b13e258 y x x
                   grind)
                | exact resolve b13e258 b13e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e63 b13e258
              have b13e2078 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have j0 := b13e1970 X0
                   grind)
                | (have r₁ := b13e1970 X0
                   have r₂ := b13e30
                   grind)
                | exact resolve b13e1970 b13e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30 b13e1970
              have b13e2090 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
                intro X0
                first
                | (have j0 := b13e2078 X0
                   grind)
                | (have r₁ := b13e2078 X0
                   have r₂ := b13e25
                   grind)
                | exact resolve b13e2078 b13e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2078
              have b13e2094 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b13e2090 x
                   have i₂ := b13e89 y x
                   grind)
                | exact superpose b13e89 b13e2090
                | exact resolve b13e2090 b13e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e89 b13e2090
              have b13e2096 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b13e2094
                   have i₂ := b13e35 y
                   grind)
                | exact superpose b13e35 b13e2094
                | exact resolve b13e2094 b13e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e35 b13e2094
              have b13e2101 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e226 y
                   have i₂ := b13e2096
                   grind)
                | exact superpose b13e2096 b13e226
                | (have j0 := b13e226 y
                   grind)
                | (have r₁ := b13e226 y
                   have r₂ := b13e2096
                   grind)
                | exact resolve b13e226 b13e2096
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e226 b13e2096
              have b13e2113 : (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by grind
              clear b13e2101
              have b13e2258 : (σ y) = (σ (M.op (M.op y y) y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e1370 y (M.op y y)
                   have i₂ := b13e2113
                   grind)
                | exact superpose b13e2113 b13e1370
                | (have j0 := b13e1370 y (M.op y y)
                   grind)
                | exact resolve b13e1370 b13e2113
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1370 b13e2113
              have b13e2312 : (σ y) = (σ (M.op y (M.op y y))) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e2258
                   have i₂ := b13e15 y y
                   grind)
                | exact superpose b13e15 b13e2258
                | exact resolve b13e2258 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2258
              have b13e2320 : (σ x) = (σ y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e2312
                   have i₂ := b13e50
                   grind)
                | exact superpose b13e50 b13e2312
                | exact resolve b13e2312 b13e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2312
              have b13e2324 : (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have r₁ := b13e2320
                   have r₂ := b13e25
                   grind)
                | exact resolve b13e2320 b13e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2320
              have b13e2327 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e2324
                   have i₂ := b13e15 y y
                   grind)
                | exact superpose b13e15 b13e2324
                | exact resolve b13e2324 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2324
              have b13e2330 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b13e2327
                   have i₂ := b13e50
                   grind)
                | exact superpose b13e50 b13e2327
                | exact resolve b13e2327 b13e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2327
              have b13e2520 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b13e16 (M.op y y)
                   have i₂ := b13e2330
                   grind)
                | exact superpose b13e2330 b13e16
                | exact resolve b13e16 b13e2330
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2330
              have b13e2569 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b13e2520
                   have i₂ := b13e16 y
                   grind)
                | exact superpose b13e16 b13e2520
                | exact resolve b13e2520 b13e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2520
              have b13e2570 : x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b13e2569
              have b13e2674 : (M.op y x) = (M.op (M.op y x) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b13e45 y
                   have i₂ := b13e2570
                   grind)
                | exact superpose b13e2570 b13e45
                | exact resolve b13e45 b13e2570
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e45 b13e2570
              have b13e2713 : y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b13e2674
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e2674
                | exact resolve b13e2674 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2674
              have b13e2714 : y = (M.op y y) := by grind
              clear b13e2713
              have b13e2826 : x = (M.op y y) := by
                first
                | (have i₁ := b13e50
                   have i₂ := b13e2714
                   grind)
                | exact superpose b13e2714 b13e50
                | exact resolve b13e50 b13e2714
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e50
              have b13e2858 : x = y := by
                first
                | (have i₁ := b13e2826
                   have i₂ := b13e2714
                   grind)
                | exact superpose b13e2714 b13e2826
                | exact resolve b13e2826 b13e2714
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2714 b13e2826
              have b13e2867 : False := by grind
              exact b13e2867
            · have b14e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op y x) := by grind
              have b14e25 : (σ x) ≠ (σ y) := by grind
              have b14e27 : x ≠ y := by grind
              have b14e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b14e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b14e33
              have b14e44 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
                intro X0
                first
                | (have i₁ := b14e15 X0 (M.op x X0)
                   have i₂ := b14e15 X0 x
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 X0
                   have i₂ := b14e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b14e20 b14e21
                | (have j1 := b14e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b14e21 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e80 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 (σ X0) X1
                   have i₂ := b14e34 X0
                   grind)
                | exact superpose b14e34 b14e15
                | exact resolve b14e15 b14e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e231 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e62 x y
                   grind)
                | exact superpose b14e62 b14e22
                | (have j1 := b14e62 x y
                   grind)
                | exact resolve b14e22 b14e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e245 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b14e231
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e231 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e231
              have b14e855 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b14e245
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e245
                | (have j1 := b14e20 y x
                   grind)
                | (have r₁ := b14e245
                   have r₂ := b14e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b14e245
                   have r₂ := b14e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b14e245 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e245
              have b14e856 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
              clear b14e855
              have b14e857 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
                first
                | (have r₁ := b14e856
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e856 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e856
              have b14e858 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b14e857
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e857 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e857
              have b14e862 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b14e80 y (σ x)
                   have i₂ := b14e858
                   grind)
                | exact superpose b14e858 b14e80
                | exact resolve b14e80 b14e858
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e80
              have b14e864 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b14e19 (σ y) (σ x)
                   have i₂ := b14e858
                   grind)
                | exact superpose b14e858 b14e19
                | (have j0 := b14e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b14e19 (σ y) (σ x)
                   have r₂ := b14e858
                   grind)
                | exact resolve b14e19 b14e858
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e868 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
              clear b14e864
              have b14e872 : (σ y) = (k (σ y) (σ x)) := by
                first
                | (have r₁ := b14e868
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e868 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e868
              have b14e874 : (σ x) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b14e862
                   have i₂ := b14e858
                   grind)
                | exact superpose b14e858 b14e862
                | exact resolve b14e862 b14e858
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e858 b14e862
              have b14e879 : (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e872
                   have i₂ := b14e21 y x
                   grind)
                | exact superpose b14e21 b14e872
                | exact resolve b14e872 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e872
              have b14e1021 : (k y x) = (τ (σ y)) := by
                first
                | (have i₁ := b14e16 (k y x)
                   have i₂ := b14e879
                   grind)
                | exact superpose b14e879 b14e16
                | exact resolve b14e16 b14e879
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e879
              have b14e1062 : y = (k y x) := by
                first
                | (have i₁ := b14e1021
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e1021
                | exact resolve b14e1021 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1021
              have b14e1130 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b14e20 y x
                   have i₂ := b14e1062
                   grind)
                | exact superpose b14e1062 b14e20
                | (have j0 := b14e20 y x
                   grind)
                | exact resolve b14e20 b14e1062
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1062
              have b14e1131 : y = (M.op x y) ∨ x = y := by
                first
                | (have r₁ := b14e1130
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e1130 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1130
              have b14e1133 : y = (M.op x y) := by
                first
                | (have r₁ := b14e1131
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e1131 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1131
              have b14e1185 : (M.op y y) = (M.op y (M.op y y)) := by
                first
                | (have i₁ := b14e15 y x
                   have i₂ := b14e1133
                   grind)
                | exact superpose b14e1133 b14e15
                | exact resolve b14e15 b14e1133
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1133
              have b14e1382 : (σ x) = (σ (k (M.op y y) y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e62 y (M.op y y)
                   have i₂ := b14e874
                   grind)
                | exact superpose b14e874 b14e62
                | (have j0 := b14e62 x (k (M.op y y) y)
                   grind)
                | exact resolve b14e62 b14e874
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e62
              have b14e1390 : (σ x) = (σ (k (M.op y y) y)) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have r₁ := b14e1382
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e1382 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1382
              have b14e3754 : (k (M.op y y) y) = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e16 (k (M.op y y) y)
                   have i₂ := b14e1390
                   grind)
                | exact superpose b14e1390 b14e16
                | exact resolve b14e16 b14e1390
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1390
              have b14e3808 : x = (k (M.op y y) y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e3754
                   have i₂ := b14e16 x
                   grind)
                | exact superpose b14e16 b14e3754
                | exact resolve b14e3754 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e3754
              have b14e3829 : x = (M.op y (M.op y y)) ∨ y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e20 (M.op y y) y
                   have i₂ := b14e3808
                   grind)
                | exact superpose b14e3808 b14e20
                | (have j0 := b14e20 (M.op y y) y
                   grind)
                | exact resolve b14e20 b14e3808
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e3808
              have b14e3837 : x = (M.op y y) ∨ y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e3829
                   have i₂ := b14e1185
                   grind)
                | exact superpose b14e1185 b14e3829
                | exact resolve b14e3829 b14e1185
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e3829
              have b14e3839 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e3837
                   have i₂ := b14e1185
                   grind)
                | exact superpose b14e1185 b14e3837
                | exact resolve b14e3837 b14e1185
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1185 b14e3837
              have b14e3840 : (σ y) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b14e3839
              have b14e6724 : (τ (σ y)) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e16 (M.op y y)
                   have i₂ := b14e3840
                   grind)
                | exact superpose b14e3840 b14e16
                | exact resolve b14e16 b14e3840
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e3840
              have b14e6784 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e6724
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e6724
                | exact resolve b14e6724 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6724
              have b14e6785 : x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b14e6784
              have b14e7012 : (M.op y x) = (M.op (M.op y x) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e44 y
                   have i₂ := b14e6785
                   grind)
                | exact superpose b14e6785 b14e44
                | exact resolve b14e44 b14e6785
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44 b14e6785
              have b14e7065 : y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e7012
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e7012
                | exact resolve b14e7012 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7012
              have b14e7066 : y = (M.op y y) := by grind
              clear b14e7065
              have b14e7289 : (σ x) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b14e874
                   have i₂ := b14e7066
                   grind)
                | exact superpose b14e7066 b14e874
                | exact resolve b14e874 b14e7066
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e874
              have b14e7326 : (σ x) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e7289
                   have i₂ := b14e34 y
                   grind)
                | exact superpose b14e34 b14e7289
                | exact resolve b14e7289 b14e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e34 b14e7289
              have b14e7333 : (σ x) = (σ y) := by
                first
                | (have i₁ := b14e7326
                   have i₂ := b14e7066
                   grind)
                | exact superpose b14e7066 b14e7326
                | exact resolve b14e7326 b14e7066
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7066 b14e7326
              have b14e7338 : False := by grind
              exact b14e7338
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b15e24 : (σ x) ≠ (σ y) := by grind
            have b15e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e33 : False := by grind
            exact b15e33
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                grind
              have b16e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b16e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b16e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b16e24 : y = (M.op y x) := by grind
              have b16e25 : (σ x) ≠ (σ y) := by grind
              have b16e27 : x ≠ y := by grind
              have b16e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : (σ x) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b16e22
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e22
                | exact resolve b16e22 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b16e21 (τ X0) X1
                   have i₂ := b16e17 X0
                   grind)
                | exact superpose b16e17 b16e21
                | exact resolve b16e21 b16e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b16e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b16e34
              have b16e44 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e15 X1 X2
                   have i₂ := b16e15 X1 X0
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e45 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
                intro X0
                first
                | (have i₁ := b16e15 X0 (M.op x X0)
                   have i₂ := b16e15 X0 x
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e46 : (M.op x y) = (M.op y (M.op y y)) := by
                first
                | (have i₁ := b16e15 y x
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e15
                | exact resolve b16e15 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e49 : x = (M.op y (M.op y y)) := by
                first
                | (have i₁ := b16e46
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e46
                | exact resolve b16e46 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e46
              have b16e51 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e19 X0 (M.op X1 X0)
                   have i₂ := b16e15 X0 X1
                   grind)
                | exact superpose b16e15 b16e19
                | (have j0 := b16e19 (M.op X1 X0) X0
                   grind)
                | exact resolve b16e19 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e52 : x ≠ x ∨ x = y ∨ y = (k y x) := by
                first
                | (have i₁ := b16e19 y x
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e19
                | (have j0 := b16e19 x y
                   grind)
                | (have r₁ := b16e19 y x
                   have r₂ := b16e28
                   grind)
                | exact resolve b16e19 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e56 : x = y ∨ y = (k y x) := by grind
              clear b16e52
              have b16e58 : y = (k y x) := by
                first
                | (have r₁ := b16e56
                   have r₂ := b16e27
                   grind)
                | exact resolve b16e56 b16e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e56
              have b16e61 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b16e21 X1 X0
                   have i₂ := b16e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b16e20 b16e21
                | (have j1 := b16e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b16e21 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e62 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e31 X1 X0
                   have i₂ := b16e20 (τ X1) X0
                   grind)
                | exact superpose b16e20 b16e31
                | (have j1 := b16e20 (τ X1) X0
                   grind)
                | exact resolve b16e31 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e31
              have b16e82 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 (σ X0) X1
                   have i₂ := b16e35 X0
                   grind)
                | exact superpose b16e35 b16e15
                | exact resolve b16e15 b16e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e217 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b16e51 (σ X0) (σ X0)
                   have i₂ := b16e35 X0
                   grind)
                | exact superpose b16e35 b16e51
                | exact resolve b16e51 b16e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e51
              have b16e220 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b16e217 X0
                   have i₂ := b16e21 X0 (M.op X0 X0)
                   grind)
                | exact superpose b16e21 b16e217
                | (have j0 := b16e217 X0
                   grind)
                | exact resolve b16e217 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e217
              have b16e249 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X0)) = (M.op (M.op X2 (σ X0)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e44 (σ X1) (σ X0) X2
                   have i₂ := b16e61 X1 X0
                   grind)
                | exact superpose b16e61 b16e44
                | (have j1 := b16e61 X1 X0
                   grind)
                | exact resolve b16e44 b16e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e44 b16e61
              have b16e1175 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                first
                | (have i₁ := b16e62 X0 (σ X0)
                   have i₂ := b16e16 X0
                   grind)
                | exact superpose b16e16 b16e62
                | exact resolve b16e62 b16e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e62
              have b16e1227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                first
                | (have i₁ := b16e1175 X0 X1
                   have i₂ := b16e21 X0 X1
                   grind)
                | exact superpose b16e21 b16e1175
                | (have j0 := b16e1175 X0 X1
                   grind)
                | exact resolve b16e1175 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e1175
              have b16e1803 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have i₁ := b16e249 y x X0
                   have i₂ := b16e58
                   grind)
                | exact superpose b16e58 b16e249
                | (have j0 := b16e249 y x x
                   grind)
                | exact resolve b16e249 b16e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e58 b16e249
              have b16e1898 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have j0 := b16e1803 X0
                   grind)
                | (have r₁ := b16e1803 X0
                   have r₂ := b16e30
                   grind)
                | exact resolve b16e1803 b16e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e30 b16e1803
              have b16e1911 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ y) (σ y)) := by
                intro X0
                first
                | (have j0 := b16e1898 X0
                   grind)
                | (have r₁ := b16e1898 X0
                   have r₂ := b16e25
                   grind)
                | exact resolve b16e1898 b16e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e1898
              have b16e1916 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (σ (M.op y y)) := by
                intro X0
                first
                | (have i₁ := b16e1911 X0
                   have i₂ := b16e35 y
                   grind)
                | exact superpose b16e35 b16e1911
                | exact resolve b16e1911 b16e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e35 b16e1911
              have b16e1919 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b16e1916 x
                   have i₂ := b16e82 y x
                   grind)
                | exact superpose b16e82 b16e1916
                | exact resolve b16e1916 b16e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e82 b16e1916
              have b16e1925 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e220 y
                   have i₂ := b16e1919
                   grind)
                | exact superpose b16e1919 b16e220
                | (have j0 := b16e220 y
                   grind)
                | (have r₁ := b16e220 y
                   have r₂ := b16e1919
                   grind)
                | exact resolve b16e220 b16e1919
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e220 b16e1919
              have b16e1937 : (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by grind
              clear b16e1925
              have b16e2165 : (σ y) = (σ (M.op (M.op y y) y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e1227 y (M.op y y)
                   have i₂ := b16e1937
                   grind)
                | exact superpose b16e1937 b16e1227
                | (have j0 := b16e1227 y (M.op y y)
                   grind)
                | exact resolve b16e1227 b16e1937
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e1227 b16e1937
              have b16e2220 : (σ y) = (σ (M.op y (M.op y y))) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e2165
                   have i₂ := b16e15 y y
                   grind)
                | exact superpose b16e15 b16e2165
                | exact resolve b16e2165 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2165
              have b16e2228 : (σ x) = (σ y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e2220
                   have i₂ := b16e49
                   grind)
                | exact superpose b16e49 b16e2220
                | exact resolve b16e2220 b16e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2220
              have b16e2232 : (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have r₁ := b16e2228
                   have r₂ := b16e25
                   grind)
                | exact resolve b16e2228 b16e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2228
              have b16e2235 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e2232
                   have i₂ := b16e15 y y
                   grind)
                | exact superpose b16e15 b16e2232
                | exact resolve b16e2232 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2232
              have b16e2238 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b16e2235
                   have i₂ := b16e49
                   grind)
                | exact superpose b16e49 b16e2235
                | exact resolve b16e2235 b16e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2235
              have b16e2749 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b16e16 (M.op y y)
                   have i₂ := b16e2238
                   grind)
                | exact superpose b16e2238 b16e16
                | exact resolve b16e16 b16e2238
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2238
              have b16e2798 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b16e2749
                   have i₂ := b16e16 y
                   grind)
                | exact superpose b16e16 b16e2749
                | exact resolve b16e2749 b16e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2749
              have b16e2799 : x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b16e2798
              have b16e2814 : (M.op y x) = (M.op (M.op y x) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b16e45 y
                   have i₂ := b16e2799
                   grind)
                | exact superpose b16e2799 b16e45
                | exact resolve b16e45 b16e2799
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e45 b16e2799
              have b16e2850 : y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b16e2814
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e2814
                | exact resolve b16e2814 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2814
              have b16e2851 : y = (M.op y y) := by grind
              clear b16e2850
              have b16e2867 : x = (M.op y y) := by
                first
                | (have i₁ := b16e49
                   have i₂ := b16e2851
                   grind)
                | exact superpose b16e2851 b16e49
                | exact resolve b16e49 b16e2851
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e49
              have b16e2900 : x = y := by
                first
                | (have i₁ := b16e2867
                   have i₂ := b16e2851
                   grind)
                | exact superpose b16e2851 b16e2867
                | exact resolve b16e2867 b16e2851
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2851 b16e2867
              have b16e2909 : False := by grind
              exact b16e2909
            · have b17e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e24 : y = (M.op y x) := by grind
              have b17e25 : (σ x) ≠ (σ y) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e27 : x ≠ y := by grind
              have b17e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b17e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b17e33
              have b17e43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 X2
                   have i₂ := b17e15 X1 X0
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e44 : (M.op y x) = (M.op x (M.op x x)) := by
                first
                | (have i₁ := b17e15 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e45 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
                intro X0
                first
                | (have i₁ := b17e15 X0 (M.op x X0)
                   have i₂ := b17e15 X0 x
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e46 : y = (M.op x (M.op x x)) := by
                first
                | (have i₁ := b17e44
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e44
                | exact resolve b17e44 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e44
              have b17e48 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e19 X0 (M.op X1 X0)
                   have i₂ := b17e15 X0 X1
                   grind)
                | exact superpose b17e15 b17e19
                | (have j0 := b17e19 (M.op X1 X0) X0
                   grind)
                | exact resolve b17e19 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e50 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
              have b17e51 : x = y ∨ x = (k x y) := by grind
              clear b17e50
              have b17e52 : x = (k x y) := by
                first
                | (have r₁ := b17e51
                   have r₂ := b17e27
                   grind)
                | exact resolve b17e51 b17e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e51
              have b17e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X1 X0
                   have i₂ := b17e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e73 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 (σ X0) X1
                   have i₂ := b17e34 X0
                   grind)
                | exact superpose b17e34 b17e15
                | exact resolve b17e15 b17e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e129 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b17e45 (σ X0)
                   have i₂ := b17e34 X0
                   grind)
                | exact superpose b17e34 b17e45
                | exact resolve b17e45 b17e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e45
              have b17e195 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b17e48 (σ X0) (σ X0)
                   have i₂ := b17e34 X0
                   grind)
                | exact superpose b17e34 b17e48
                | exact resolve b17e48 b17e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e48
              have b17e198 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e195 X0
                   have i₂ := b17e21 X0 (M.op X0 X0)
                   grind)
                | exact superpose b17e21 b17e195
                | (have j0 := b17e195 X0
                   grind)
                | exact resolve b17e195 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e195
              have b17e223 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b17e22
                   have i₂ := b17e55 x y
                   grind)
                | exact superpose b17e55 b17e22
                | (have j1 := b17e55 x y
                   grind)
                | exact resolve b17e22 b17e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e227 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X0)) = (M.op (M.op X2 (σ X0)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e43 (σ X1) (σ X0) X2
                   have i₂ := b17e55 X1 X0
                   grind)
                | exact superpose b17e55 b17e43
                | (have j1 := b17e55 X1 X0
                   grind)
                | exact resolve b17e43 b17e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e43 b17e55
              have b17e235 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b17e223
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e223 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e223
              have b17e728 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b17e235
                   have i₂ := b17e20 y x
                   grind)
                | exact superpose b17e20 b17e235
                | (have j1 := b17e20 y x
                   grind)
                | (have r₁ := b17e235
                   have r₂ := b17e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b17e235
                   have r₂ := b17e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b17e235 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e235
              have b17e729 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
              clear b17e728
              have b17e730 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
                first
                | (have r₁ := b17e729
                   have r₂ := b17e28
                   grind)
                | exact resolve b17e729 b17e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e729
              have b17e731 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b17e730
                   have r₂ := b17e27
                   grind)
                | exact resolve b17e730 b17e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e730
              have b17e1426 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have i₁ := b17e227 x y X0
                   have i₂ := b17e52
                   grind)
                | exact superpose b17e52 b17e227
                | (have j0 := b17e227 x y x
                   grind)
                | exact resolve b17e227 b17e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e52 b17e227
              have b17e1525 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have j0 := b17e1426 X0
                   grind)
                | (have r₁ := b17e1426 X0
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e1426 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1426
              have b17e1538 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ x) (σ x)) := by
                intro X0
                first
                | (have j0 := b17e1525 X0
                   grind)
                | (have r₁ := b17e1525 X0
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e1525 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1525
              have b17e1544 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (σ (M.op x x)) := by
                intro X0
                first
                | (have i₁ := b17e1538 X0
                   have i₂ := b17e34 x
                   grind)
                | exact superpose b17e34 b17e1538
                | exact resolve b17e1538 b17e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1538
              have b17e1548 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b17e1544 x
                   have i₂ := b17e73 x x
                   grind)
                | exact superpose b17e73 b17e1544
                | exact resolve b17e1544 b17e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e73 b17e1544
              have b17e1935 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b17e198 x
                   have i₂ := b17e1548
                   grind)
                | exact superpose b17e1548 b17e198
                | (have j0 := b17e198 x
                   grind)
                | (have r₁ := b17e198 x
                   have r₂ := b17e1548
                   grind)
                | exact resolve b17e198 b17e1548
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e198 b17e1548
              have b17e1946 : (σ x) = (σ (k x (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by grind
              clear b17e1935
              have b17e3569 : (σ x) = (σ (M.op (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e1946
                   have i₂ := b17e20 x (M.op x x)
                   grind)
                | exact superpose b17e20 b17e1946
                | (have j1 := b17e20 x (M.op x x)
                   grind)
                | exact resolve b17e1946 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1946
              have b17e3632 : (σ x) = (σ (M.op x (M.op x x))) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e3569
                   have i₂ := b17e15 x x
                   grind)
                | exact superpose b17e15 b17e3569
                | exact resolve b17e3569 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3569
              have b17e3637 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e3632
                   have i₂ := b17e46
                   grind)
                | exact superpose b17e46 b17e3632
                | exact resolve b17e3632 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3632
              have b17e3638 : (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
                first
                | (have r₁ := b17e3637
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e3637 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3637
              have b17e3639 : (M.op x x) = (M.op x (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e3638
                   have i₂ := b17e15 x x
                   grind)
                | exact superpose b17e15 b17e3638
                | exact resolve b17e3638 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3638
              have b17e3640 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e3639
                   have i₂ := b17e46
                   grind)
                | exact superpose b17e46 b17e3639
                | exact resolve b17e3639 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3639
              have b17e6659 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e16 (M.op x x)
                   have i₂ := b17e3640
                   grind)
                | exact superpose b17e3640 b17e16
                | exact resolve b17e16 b17e3640
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3640
              have b17e6719 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e6659
                   have i₂ := b17e16 x
                   grind)
                | exact superpose b17e16 b17e6659
                | exact resolve b17e6659 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e6659
              have b17e6720 : x = (M.op x x) ∨ y = (M.op x x) := by grind
              clear b17e6719
              have b17e6928 : y = (M.op x x) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b17e46
                   have i₂ := b17e6720
                   grind)
                | exact superpose b17e6720 b17e46
                | exact resolve b17e46 b17e6720
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46 b17e6720
              have b17e6957 : y = (M.op x x) := by grind
              clear b17e6928
              have b17e7242 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
                first
                | (have i₁ := b17e129 x
                   have i₂ := b17e6957
                   grind)
                | exact superpose b17e6957 b17e129
                | exact resolve b17e129 b17e6957
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e129
              have b17e7285 : (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b17e7242
                   have i₂ := b17e731
                   grind)
                | exact superpose b17e731 b17e7242
                | exact resolve b17e7242 b17e731
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e731 b17e7242
              have b17e7306 : (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b17e7285
                   have i₂ := b17e34 x
                   grind)
                | exact superpose b17e34 b17e7285
                | exact resolve b17e7285 b17e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e34 b17e7285
              have b17e7312 : (σ x) = (σ y) := by
                first
                | (have i₁ := b17e7306
                   have i₂ := b17e6957
                   grind)
                | exact superpose b17e6957 b17e7306
                | exact resolve b17e7306 b17e6957
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e6957 b17e7306
              have b17e7317 : False := by grind
              exact b17e7317
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b18e21 : x ≠ y := by grind
          have b18e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e30 : False := by grind
          exact b18e30
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e24 : (σ x) = (σ y) := by grind
            have b19e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 y
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e15
              | exact resolve b19e15 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e31 : x = y := by
              first
              | (have i₁ := b19e30
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e30
              | exact resolve b19e30 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : False := by grind
            exact b19e32
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e24 : (σ x) = (σ y) := by grind
            have b20e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e29 : y = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 y
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e15
              | exact resolve b20e15 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e30 : x = y := by
              first
              | (have i₁ := b20e29
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e29
              | exact resolve b20e29 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : False := by grind
            exact b20e31
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b21e24 : (σ x) ≠ (σ y) := by grind
            have b21e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e33 : False := by grind
            exact b21e33
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e24 : y ≠ (M.op y x) := by grind
              have b22e25 : (σ x) ≠ (σ y) := by grind
              have b22e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b22e27 : x ≠ y := by grind
              have b22e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b22e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b22e34
              have b22e44 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e15 X1 X2
                   have i₂ := b22e15 X1 X0
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e46 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
                first
                | (have i₁ := b22e15 (σ x) (σ y)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e15
                | exact resolve b22e15 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e49 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b22e46
                   have i₂ := b22e35 x
                   grind)
                | exact superpose b22e35 b22e46
                | exact resolve b22e46 b22e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e46
              have b22e50 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b22e49
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e49
                | exact resolve b22e49 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e49
              have b22e53 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b22e19 (σ x) (σ y)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e19
                | (have j0 := b22e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b22e19 (σ x) (σ y)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e19 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e57 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b22e53
              have b22e59 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e57
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e57 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e57
              have b22e60 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e59
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e59
                | exact resolve b22e59 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e59
              have b22e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b22e21 X1 X0
                   have i₂ := b22e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b22e20 b22e21
                | (have j1 := b22e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b22e21 b22e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e69 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e60
                   grind)
                | exact superpose b22e60 b22e16
                | exact resolve b22e16 b22e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e60
              have b22e70 : x = (k x y) := by
                first
                | (have i₁ := b22e69
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e69
                | exact resolve b22e69 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e69
              have b22e88 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e70
                   grind)
                | exact superpose b22e70 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e70
              have b22e89 : x = (M.op y x) ∨ x = y := by
                first
                | (have r₁ := b22e88
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e88 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e88
              have b22e91 : x = (M.op y x) := by
                first
                | (have r₁ := b22e89
                   have r₂ := b22e27
                   grind)
                | exact resolve b22e89 b22e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e89
              have b22e102 : (M.op x x) = (M.op x (M.op x x)) := by
                first
                | (have i₁ := b22e15 x y
                   have i₂ := b22e91
                   grind)
                | exact superpose b22e91 b22e15
                | exact resolve b22e15 b22e91
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e91
              have b22e128 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b22e44 X1 X0 (M.op x X0)
                   have i₂ := b22e15 X0 x
                   grind)
                | exact superpose b22e15 b22e44
                | exact resolve b22e44 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e44
              have b22e266 : (σ y) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b22e63 x (M.op x x)
                   have i₂ := b22e50
                   grind)
                | exact superpose b22e50 b22e63
                | (have j0 := b22e63 y (k (M.op x x) x)
                   grind)
                | exact resolve b22e63 b22e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e63
              have b22e282 : (σ y) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have r₁ := b22e266
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e266 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e266
              have b22e777 : (k (M.op x x) x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b22e16 (k (M.op x x) x)
                   have i₂ := b22e282
                   grind)
                | exact superpose b22e282 b22e16
                | exact resolve b22e16 b22e282
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e282
              have b22e811 : y = (k (M.op x x) x) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b22e777
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e777
                | exact resolve b22e777 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e777
              have b22e816 : y = (M.op x (M.op x x)) ∨ x = (M.op x (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b22e20 (M.op x x) x
                   have i₂ := b22e811
                   grind)
                | exact superpose b22e811 b22e20
                | (have j0 := b22e20 (M.op x x) x
                   grind)
                | exact resolve b22e20 b22e811
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e811
              have b22e817 : y = (M.op x x) ∨ x = (M.op x (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b22e816
                   have i₂ := b22e102
                   grind)
                | exact superpose b22e102 b22e816
                | exact resolve b22e816 b22e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e816
              have b22e819 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b22e817
                   have i₂ := b22e102
                   grind)
                | exact superpose b22e102 b22e817
                | exact resolve b22e817 b22e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e102 b22e817
              have b22e820 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
              clear b22e819
              have b22e2722 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b22e16 (M.op x x)
                   have i₂ := b22e820
                   grind)
                | exact superpose b22e820 b22e16
                | exact resolve b22e16 b22e820
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e820
              have b22e2771 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b22e2722
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e2722
                | exact resolve b22e2722 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2722
              have b22e2772 : x = (M.op x x) ∨ y = (M.op x x) := by grind
              clear b22e2771
              have b22e2876 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b22e50
                   have i₂ := b22e2772
                   grind)
                | exact superpose b22e2772 b22e50
                | exact resolve b22e50 b22e2772
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e50 b22e2772
              have b22e2904 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b22e2876
                   have i₂ := b22e35 x
                   grind)
                | exact superpose b22e35 b22e2876
                | exact resolve b22e2876 b22e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e35 b22e2876
              have b22e3012 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b22e16 (M.op x x)
                   have i₂ := b22e2904
                   grind)
                | exact superpose b22e2904 b22e16
                | exact resolve b22e16 b22e2904
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2904
              have b22e3063 : y = (M.op x x) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b22e3012
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e3012
                | exact resolve b22e3012 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3012
              have b22e3064 : y = (M.op x x) := by grind
              clear b22e3063
              have b22e3098 : (M.op y x) = (M.op (M.op x y) x) := by
                first
                | (have i₁ := b22e128 x x
                   have i₂ := b22e3064
                   grind)
                | exact superpose b22e3064 b22e128
                | exact resolve b22e128 b22e3064
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e128
              have b22e3102 : (M.op y x) = (M.op x x) := by
                first
                | (have i₁ := b22e3098
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e3098
                | exact resolve b22e3098 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3098
              have b22e3116 : y = (M.op y x) := by
                first
                | (have i₁ := b22e3102
                   have i₂ := b22e3064
                   grind)
                | exact superpose b22e3064 b22e3102
                | exact resolve b22e3102 b22e3064
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3064 b22e3102
              have b22e3126 : False := by grind
              exact b22e3126
            · have b23e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e24 : y ≠ (M.op y x) := by grind
              have b23e25 : (σ x) ≠ (σ y) := by grind
              have b23e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b23e27 : x ≠ y := by grind
              have b23e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b23e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b23e33
              have b23e44 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
                first
                | (have i₁ := b23e15 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e46 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b23e44
                   have i₂ := b23e34 x
                   grind)
                | exact superpose b23e34 b23e44
                | exact resolve b23e44 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e44
              have b23e47 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b23e46
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e46
                | exact resolve b23e46 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e46
              have b23e59 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
              have b23e62 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b23e59
              have b23e63 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e62
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e62 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e62
              have b23e64 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e63
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e63
                | exact resolve b23e63 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e63
              have b23e67 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e64
                   grind)
                | exact superpose b23e64 b23e16
                | exact resolve b23e16 b23e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e64
              have b23e68 : x = (k x y) := by
                first
                | (have i₁ := b23e67
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e67
                | exact resolve b23e67 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e67
              have b23e73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X1 X0
                   have i₂ := b23e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b23e20 b23e21
                | (have j1 := b23e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b23e21 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e79 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e68
                   grind)
                | exact superpose b23e68 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e68
              have b23e80 : x = (M.op y x) ∨ x = y := by
                first
                | (have r₁ := b23e79
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e79 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e79
              have b23e82 : x = (M.op y x) := by
                first
                | (have r₁ := b23e80
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e80 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e80
              have b23e93 : (M.op x x) = (M.op x (M.op x x)) := by
                first
                | (have i₁ := b23e15 x y
                   have i₂ := b23e82
                   grind)
                | exact superpose b23e82 b23e15
                | exact resolve b23e15 b23e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e244 : (σ y) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e73 x (M.op x x)
                   have i₂ := b23e47
                   grind)
                | exact superpose b23e47 b23e73
                | (have j0 := b23e73 y (k (M.op x x) x)
                   grind)
                | exact resolve b23e73 b23e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e73
              have b23e261 : (σ y) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have r₁ := b23e244
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e244 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e244
              have b23e770 : (k (M.op x x) x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e16 (k (M.op x x) x)
                   have i₂ := b23e261
                   grind)
                | exact superpose b23e261 b23e16
                | exact resolve b23e16 b23e261
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e261
              have b23e806 : y = (k (M.op x x) x) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e770
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e770
                | exact resolve b23e770 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e770
              have b23e811 : y = (M.op x (M.op x x)) ∨ x = (M.op x (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e20 (M.op x x) x
                   have i₂ := b23e806
                   grind)
                | exact superpose b23e806 b23e20
                | (have j0 := b23e20 (M.op x x) x
                   grind)
                | exact resolve b23e20 b23e806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e806
              have b23e812 : y = (M.op x x) ∨ x = (M.op x (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e811
                   have i₂ := b23e93
                   grind)
                | exact superpose b23e93 b23e811
                | exact resolve b23e811 b23e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e811
              have b23e814 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e812
                   have i₂ := b23e93
                   grind)
                | exact superpose b23e93 b23e812
                | exact resolve b23e812 b23e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e93 b23e812
              have b23e815 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
              clear b23e814
              have b23e4313 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b23e16 (M.op x x)
                   have i₂ := b23e815
                   grind)
                | exact superpose b23e815 b23e16
                | exact resolve b23e16 b23e815
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e815
              have b23e4367 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b23e4313
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e4313
                | exact resolve b23e4313 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4313
              have b23e4368 : x = (M.op x x) ∨ y = (M.op x x) := by grind
              clear b23e4367
              have b23e4607 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b23e47
                   have i₂ := b23e4368
                   grind)
                | exact superpose b23e4368 b23e47
                | exact resolve b23e47 b23e4368
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e47 b23e4368
              have b23e4642 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b23e4607
                   have i₂ := b23e34 x
                   grind)
                | exact superpose b23e34 b23e4607
                | exact resolve b23e4607 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34 b23e4607
              have b23e4766 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b23e16 (M.op x x)
                   have i₂ := b23e4642
                   grind)
                | exact superpose b23e4642 b23e16
                | exact resolve b23e16 b23e4642
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4642
              have b23e4825 : y = (M.op x x) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b23e4766
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e4766
                | exact resolve b23e4766 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4766
              have b23e4826 : y = (M.op x x) := by grind
              clear b23e4825
              have b23e5080 : (M.op x y) = (M.op y x) := by
                first
                | (have i₁ := b23e15 x x
                   have i₂ := b23e4826
                   grind)
                | exact superpose b23e4826 b23e15
                | exact resolve b23e15 b23e4826
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4826
              have b23e5095 : x = (M.op x y) := by
                first
                | (have i₁ := b23e5080
                   have i₂ := b23e82
                   grind)
                | exact superpose b23e82 b23e5080
                | exact resolve b23e5080 b23e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e82 b23e5080
              have b23e5116 : False := by grind
              exact b23e5116
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b24e24 : (σ x) ≠ (σ y) := by grind
            have b24e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e33 : False := by grind
            exact b24e33
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e25 : (σ x) ≠ (σ y) := by grind
              have b25e27 : x ≠ y := by grind
              have b25e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : (σ x) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e22
                | exact resolve b25e22 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b25e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b25e34
              have b25e44 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X1 X2
                   have i₂ := b25e15 X1 X0
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e45 : (M.op x y) = (M.op y (M.op y y)) := by
                first
                | (have i₁ := b25e15 y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e47 : x = (M.op y (M.op y y)) := by
                first
                | (have i₁ := b25e45
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e45
                | exact resolve b25e45 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e45
              have b25e49 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b25e19 X0 (M.op X1 X0)
                   have i₂ := b25e15 X0 X1
                   grind)
                | exact superpose b25e15 b25e19
                | (have j0 := b25e19 (M.op X1 X0) X0
                   grind)
                | exact resolve b25e19 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e50 : x ≠ x ∨ x = y ∨ y = (k y x) := by
                first
                | (have i₁ := b25e19 y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e19
                | (have j0 := b25e19 x y
                   grind)
                | (have r₁ := b25e19 y x
                   have r₂ := b25e28
                   grind)
                | exact resolve b25e19 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e52 : x = y ∨ y = (k y x) := by grind
              clear b25e50
              have b25e53 : y = (k y x) := by
                first
                | (have r₁ := b25e52
                   have r₂ := b25e27
                   grind)
                | exact resolve b25e52 b25e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e52
              have b25e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
              have b25e74 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 (σ X0) X1
                   have i₂ := b25e35 X0
                   grind)
                | exact superpose b25e35 b25e15
                | exact resolve b25e15 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e103 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e44 X1 (σ X0) (σ X0)
                   have i₂ := b25e35 X0
                   grind)
                | exact superpose b25e35 b25e44
                | exact resolve b25e44 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e196 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b25e49 (σ X0) (σ X0)
                   have i₂ := b25e35 X0
                   grind)
                | exact superpose b25e35 b25e49
                | exact resolve b25e49 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e49
              have b25e199 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e196 X0
                   have i₂ := b25e21 X0 (M.op X0 X0)
                   grind)
                | exact superpose b25e21 b25e196
                | (have j0 := b25e196 X0
                   grind)
                | exact resolve b25e196 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e196
              have b25e228 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X0)) = (M.op (M.op X2 (σ X0)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e44 (σ X1) (σ X0) X2
                   have i₂ := b25e56 X1 X0
                   grind)
                | exact superpose b25e56 b25e44
                | (have j1 := b25e56 X1 X0
                   grind)
                | exact resolve b25e44 b25e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44 b25e56
              have b25e1641 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have i₁ := b25e228 y x X0
                   have i₂ := b25e53
                   grind)
                | exact superpose b25e53 b25e228
                | (have j0 := b25e228 y x x
                   grind)
                | exact resolve b25e228 b25e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e53 b25e228
              have b25e1734 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have j0 := b25e1641 X0
                   grind)
                | (have r₁ := b25e1641 X0
                   have r₂ := b25e30
                   grind)
                | exact resolve b25e1641 b25e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1641
              have b25e1746 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ y) (σ y)) := by
                intro X0
                first
                | (have j0 := b25e1734 X0
                   grind)
                | (have r₁ := b25e1734 X0
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e1734 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1734
              have b25e1750 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (σ (M.op y y)) := by
                intro X0
                first
                | (have i₁ := b25e1746 X0
                   have i₂ := b25e35 y
                   grind)
                | exact superpose b25e35 b25e1746
                | exact resolve b25e1746 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35 b25e1746
              have b25e1752 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b25e1750 x
                   have i₂ := b25e74 y x
                   grind)
                | exact superpose b25e74 b25e1750
                | exact resolve b25e1750 b25e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1750
              have b25e1757 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b25e199 y
                   have i₂ := b25e1752
                   grind)
                | exact superpose b25e1752 b25e199
                | (have j0 := b25e199 y
                   grind)
                | (have r₁ := b25e199 y
                   have r₂ := b25e1752
                   grind)
                | exact resolve b25e199 b25e1752
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e199
              have b25e1769 : (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by grind
              clear b25e1757
              have b25e1904 : (σ y) = (σ (M.op (M.op y y) y)) ∨ (σ y) = (σ (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e1769
                   have i₂ := b25e20 y (M.op y y)
                   grind)
                | exact superpose b25e20 b25e1769
                | (have j1 := b25e20 y (M.op y y)
                   grind)
                | exact resolve b25e1769 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1769
              have b25e1962 : (σ y) = (σ (M.op y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e1904
                   have i₂ := b25e15 y y
                   grind)
                | exact superpose b25e15 b25e1904
                | exact resolve b25e1904 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1904
              have b25e1967 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e1962
                   have i₂ := b25e47
                   grind)
                | exact superpose b25e47 b25e1962
                | exact resolve b25e1962 b25e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1962
              have b25e1968 : (σ y) = (σ (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have r₁ := b25e1967
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e1967 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1967
              have b25e1969 : (M.op y y) = (M.op y (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e1968
                   have i₂ := b25e15 y y
                   grind)
                | exact superpose b25e15 b25e1968
                | exact resolve b25e1968 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1968
              have b25e1970 : (σ y) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e1969
                   have i₂ := b25e47
                   grind)
                | exact superpose b25e47 b25e1969
                | exact resolve b25e1969 b25e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1969
              have b25e2321 : (M.op y y) = (τ (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e16 (M.op y y)
                   have i₂ := b25e1970
                   grind)
                | exact superpose b25e1970 b25e16
                | exact resolve b25e16 b25e1970
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1970
              have b25e2370 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e2321
                   have i₂ := b25e16 y
                   grind)
                | exact superpose b25e16 b25e2321
                | exact resolve b25e2321 b25e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2321
              have b25e2371 : x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b25e2370
              have b25e2486 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y y) := by
                intro X0
                first
                | (have i₁ := b25e103 y X0
                   have i₂ := b25e2371
                   grind)
                | exact superpose b25e2371 b25e103
                | exact resolve b25e103 b25e2371
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e103
              have b25e2515 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e2486 x
                   have i₂ := b25e74 y x
                   grind)
                | exact superpose b25e74 b25e2486
                | exact resolve b25e2486 b25e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e74 b25e2486
              have b25e2525 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e2515
                   have i₂ := b25e1752
                   grind)
                | exact superpose b25e1752 b25e2515
                | exact resolve b25e2515 b25e1752
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1752 b25e2515
              have b25e3962 : (σ x) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e30
                   have i₂ := b25e2525
                   grind)
                | exact superpose b25e2525 b25e30
                | exact resolve b25e30 b25e2525
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e30 b25e2525
              have b25e4284 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e3962
                   have i₂ := b25e2371
                   grind)
                | exact superpose b25e2371 b25e3962
                | exact resolve b25e3962 b25e2371
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2371 b25e3962
              have b25e4287 : x = y ∨ y = (M.op y y) := by grind
              clear b25e4284
              have b25e4288 : y = (M.op y y) := by
                first
                | (have r₁ := b25e4287
                   have r₂ := b25e27
                   grind)
                | exact resolve b25e4287 b25e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4287
              have b25e4391 : x = (M.op y y) := by
                first
                | (have i₁ := b25e47
                   have i₂ := b25e4288
                   grind)
                | exact superpose b25e4288 b25e47
                | exact resolve b25e47 b25e4288
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e47
              have b25e4434 : x = y := by
                first
                | (have i₁ := b25e4391
                   have i₂ := b25e4288
                   grind)
                | exact superpose b25e4288 b25e4391
                | exact resolve b25e4391 b25e4288
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4288 b25e4391
              have b25e4444 : False := by grind
              exact b25e4444
            · have b26e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e24 : y ≠ (M.op y x) := by grind
              have b26e25 : (σ x) ≠ (σ y) := by grind
              have b26e27 : x ≠ y := by grind
              have b26e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b26e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b26e33
              have b26e61 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e15 (σ X0) X1
                   have i₂ := b26e34 X0
                   grind)
                | exact superpose b26e34 b26e15
                | exact resolve b26e15 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
              have b26e202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e65 x y
                   grind)
                | exact superpose b26e65 b26e22
                | (have j1 := b26e65 x y
                   grind)
                | exact resolve b26e22 b26e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e214 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e202
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e202 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e202
              have b26e668 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b26e214
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e214
                | (have j1 := b26e20 y x
                   grind)
                | (have r₁ := b26e214
                   have r₂ := b26e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b26e214
                   have r₂ := b26e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b26e214 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e214
              have b26e669 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
              clear b26e668
              have b26e670 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
                first
                | (have r₁ := b26e669
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e669 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e669
              have b26e671 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e670
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e670 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e670
              have b26e675 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b26e61 y (σ x)
                   have i₂ := b26e671
                   grind)
                | exact superpose b26e671 b26e61
                | exact resolve b26e61 b26e671
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e61
              have b26e677 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b26e19 (σ y) (σ x)
                   have i₂ := b26e671
                   grind)
                | exact superpose b26e671 b26e19
                | (have j0 := b26e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b26e19 (σ y) (σ x)
                   have r₂ := b26e671
                   grind)
                | exact resolve b26e19 b26e671
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e681 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
              clear b26e677
              have b26e685 : (σ y) = (k (σ y) (σ x)) := by
                first
                | (have r₁ := b26e681
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e681 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e681
              have b26e687 : (σ x) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b26e675
                   have i₂ := b26e671
                   grind)
                | exact superpose b26e671 b26e675
                | exact resolve b26e675 b26e671
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e671 b26e675
              have b26e692 : (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e685
                   have i₂ := b26e21 y x
                   grind)
                | exact superpose b26e21 b26e685
                | exact resolve b26e685 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e685
              have b26e815 : (k y x) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (k y x)
                   have i₂ := b26e692
                   grind)
                | exact superpose b26e692 b26e16
                | exact resolve b26e16 b26e692
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e692
              have b26e854 : y = (k y x) := by
                first
                | (have i₁ := b26e815
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e815
                | exact resolve b26e815 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e815
              have b26e913 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b26e20 y x
                   have i₂ := b26e854
                   grind)
                | exact superpose b26e854 b26e20
                | (have j0 := b26e20 y x
                   grind)
                | exact resolve b26e20 b26e854
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e854
              have b26e914 : y = (M.op x y) ∨ x = y := by
                first
                | (have r₁ := b26e913
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e913 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e913
              have b26e916 : y = (M.op x y) := by
                first
                | (have r₁ := b26e914
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e914 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e914
              have b26e969 : (M.op y y) = (M.op y (M.op y y)) := by
                first
                | (have i₁ := b26e15 y x
                   have i₂ := b26e916
                   grind)
                | exact superpose b26e916 b26e15
                | exact resolve b26e15 b26e916
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1147 : (σ x) = (σ (k (M.op y y) y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e65 y (M.op y y)
                   have i₂ := b26e687
                   grind)
                | exact superpose b26e687 b26e65
                | (have j0 := b26e65 x (k (M.op y y) y)
                   grind)
                | exact resolve b26e65 b26e687
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e65
              have b26e1155 : (σ x) = (σ (k (M.op y y) y)) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have r₁ := b26e1147
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e1147 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1147
              have b26e3446 : (k (M.op y y) y) = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e16 (k (M.op y y) y)
                   have i₂ := b26e1155
                   grind)
                | exact superpose b26e1155 b26e16
                | exact resolve b26e16 b26e1155
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1155
              have b26e3500 : x = (k (M.op y y) y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e3446
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e3446
                | exact resolve b26e3446 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3446
              have b26e3630 : x = (M.op y (M.op y y)) ∨ y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e20 (M.op y y) y
                   have i₂ := b26e3500
                   grind)
                | exact superpose b26e3500 b26e20
                | (have j0 := b26e20 (M.op y y) y
                   grind)
                | exact resolve b26e20 b26e3500
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3500
              have b26e3640 : x = (M.op y y) ∨ y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e3630
                   have i₂ := b26e969
                   grind)
                | exact superpose b26e969 b26e3630
                | exact resolve b26e3630 b26e969
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3630
              have b26e3642 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e3640
                   have i₂ := b26e969
                   grind)
                | exact superpose b26e969 b26e3640
                | exact resolve b26e3640 b26e969
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e969 b26e3640
              have b26e3643 : (σ y) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b26e3642
              have b26e6176 : (M.op y y) = (τ (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b26e16 (M.op y y)
                   have i₂ := b26e3643
                   grind)
                | exact superpose b26e3643 b26e16
                | exact resolve b26e16 b26e3643
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3643
              have b26e6236 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b26e6176
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e6176
                | exact resolve b26e6176 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6176
              have b26e6237 : x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b26e6236
              have b26e6482 : (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b26e15 y y
                   have i₂ := b26e6237
                   grind)
                | exact superpose b26e6237 b26e15
                | exact resolve b26e15 b26e6237
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6237
              have b26e6504 : y = (M.op y x) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b26e6482
                   have i₂ := b26e916
                   grind)
                | exact superpose b26e916 b26e6482
                | exact resolve b26e6482 b26e916
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e916 b26e6482
              have b26e6525 : y = (M.op y y) := by
                first
                | (have r₁ := b26e6504
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e6504 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6504
              have b26e6736 : (σ x) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b26e687
                   have i₂ := b26e6525
                   grind)
                | exact superpose b26e6525 b26e687
                | exact resolve b26e687 b26e6525
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e687
              have b26e6773 : (σ x) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e6736
                   have i₂ := b26e34 y
                   grind)
                | exact superpose b26e34 b26e6736
                | exact resolve b26e6736 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34 b26e6736
              have b26e6780 : (σ x) = (σ y) := by
                first
                | (have i₁ := b26e6773
                   have i₂ := b26e6525
                   grind)
                | exact superpose b26e6525 b26e6773
                | exact resolve b26e6773 b26e6525
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6525 b26e6773
              have b26e6785 : False := by grind
              exact b26e6785

/-- `Equation4389`: `x ◇ (x ◇ x) = (y ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_y_pxy_Equation4389 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4389 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4389.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = (M.op y x) := by grind
        have b0e21 : (σ x) = (M.op (σ y) (σ x)) := by grind
        have b0e22 : y = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e19
          | exact resolve b0e19 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e35 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b0e15 (σ x) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e15
          | (have j0 := b0e15 (σ x) (σ y)
             grind)
          | (have r₁ := b0e15 (σ x) (σ y)
             have r₂ := b0e21
             grind)
          | exact resolve b0e15 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : x ≠ x ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b0e15 x y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e15
          | (have j0 := b0e15 x y
             grind)
          | (have r₁ := b0e15 x y
             have r₂ := b0e20
             grind)
          | exact resolve b0e15 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : (M.op x y) = (k x y) := by grind
        clear b0e37
        have b0e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b0e35
        have b0e41 : y = (k x y) := by
          first
          | (have i₁ := b0e38
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e38
          | exact resolve b0e38 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b0e40
             have i₂ := b0e18 x y
             grind)
          | exact superpose b0e18 b0e40
          | exact resolve b0e40 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e44 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e43
             have i₂ := b0e41
             grind)
          | exact superpose b0e41 b0e43
          | exact resolve b0e43 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e43
        have b0e45 : False := by grind
        exact b0e45
      · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
            intro X0 X1
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : x = (M.op y x) := by grind
          have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b1e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e33 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e35 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x := by
            intro X0
            first
            | (have i₁ := b1e33 X0
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e33
            | exact resolve b1e33 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e33
          have b1e36 : x = (M.op x y) := by
            first
            | (have i₁ := b1e35 x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e35
            | exact resolve b1e35 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35
          have b1e42 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          have b1e43 : x ≠ x ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b1e16 x y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e16
            | (have j0 := b1e16 x y
               grind)
            | (have r₁ := b1e16 x y
               have r₂ := b1e21
               grind)
            | exact resolve b1e16 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e45 : (M.op x y) = (k x y) := by grind
          clear b1e43
          have b1e46 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b1e42
          have b1e47 : x = (k x y) := by
            first
            | (have i₁ := b1e45
               have i₂ := b1e36
               grind)
            | exact superpose b1e36 b1e45
            | exact resolve b1e45 b1e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e45
          have b1e48 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b1e46
               have i₂ := b1e19 x y
               grind)
            | exact superpose b1e19 b1e46
            | exact resolve b1e46 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e46
          have b1e52 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e48
               have i₂ := b1e47
               grind)
            | exact superpose b1e47 b1e48
            | exact resolve b1e48 b1e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e47 b1e48
          have b1e83 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e52
               grind)
            | exact superpose b1e52 b1e20
            | exact resolve b1e20 b1e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e52
          have b1e86 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b1e83
               have i₂ := b1e36
               grind)
            | exact superpose b1e36 b1e83
            | exact resolve b1e83 b1e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e36 b1e83
          have b1e87 : False := by grind
          exact b1e87
        · have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : x = (M.op y x) := by grind
          have b2e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e44 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b2e16 (σ x) (σ y)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e16
            | (have j0 := b2e16 (σ x) (σ y)
               grind)
            | (have r₁ := b2e16 (σ x) (σ y)
               have r₂ := b2e22
               grind)
            | exact resolve b2e16 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e45 : x ≠ x ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b2e16 x y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e16
            | (have j0 := b2e16 x y
               grind)
            | (have r₁ := b2e16 x y
               have r₂ := b2e21
               grind)
            | exact resolve b2e16 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e46 : (M.op x y) = (k x y) := by grind
          clear b2e45
          have b2e47 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b2e44
          have b2e48 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b2e47
               have i₂ := b2e19 x y
               grind)
            | exact superpose b2e19 b2e47
            | exact resolve b2e47 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e47
          have b2e49 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b2e48
               have i₂ := b2e46
               grind)
            | exact superpose b2e46 b2e48
            | exact resolve b2e48 b2e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e46 b2e48
          have b2e50 : False := by grind
          exact b2e50
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
            intro X0 X1
            grind
          have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b3e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : x = (M.op y x) := by grind
          have b3e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ x) = (M.op (σ y) (σ y)) := by grind
          have b3e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e33 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b3e13 (σ y) X0
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e13
            | exact resolve b3e13 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e35 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b3e13 X0 (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e13
            | exact resolve b3e13 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e36 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X0 x
               have i₂ := b3e13 X1 x
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e74 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b3e13 X1 X2
               have i₂ := b3e18 X0 X2
               grind)
            | (have i₁ := b3e13 X0 X1
               have i₂ := b3e18 (M.op X1 X1) X1
               grind)
            | exact superpose b3e18 b3e13
            | (have j1 := b3e18 X0 X2
               grind)
            | exact resolve b3e13 b3e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e75 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b3e13 X1 X2
               have i₂ := b3e18 X0 X1
               grind)
            | (have i₁ := b3e13 X0 X1
               have i₂ := b3e18 (M.op X0 X0) X1
               grind)
            | exact superpose b3e18 b3e13
            | (have j1 := b3e18 X0 X1
               grind)
            | exact resolve b3e13 b3e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e81 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X2) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b3e75 X0 X1 X2
               have j1 := b3e16 X0 X1
               grind)
            | (have r₁ := b3e75 (M.op (M.op X2 X2) X2) X1 X2
               have r₂ := b3e16 (M.op (M.op X2 X2) X2) X1
               grind)
            | (have r₁ := b3e75 X0 X1 (M.op X1 X0)
               have r₂ := b3e16 (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))
               grind)
            | (have r₁ := b3e75 X0 X1 X2
               have r₂ := b3e16 X0 X1
               grind)
            | exact resolve b3e75 b3e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e75
          have b3e82 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b3e74 X0 X1 X2
               have j1 := b3e16 X0 X2
               grind)
            | (have r₁ := b3e74 X1 X1 X1
               have r₂ := b3e16 (M.op X1 X1) X1
               grind)
            | (have r₁ := b3e74 X1 X1 (M.op X1 (M.op X1 X1))
               have r₂ := b3e16 (M.op X1 (M.op X1 X1)) X1
               grind)
            | (have r₁ := b3e74 X0 X1 X1
               have r₂ := b3e16 X0 X1
               grind)
            | exact resolve b3e74 b3e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e74
          have b3e86 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (σ x)) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b3e81 X0 X1 x
               have i₂ := b3e33 x
               grind)
            | exact superpose b3e33 b3e81
            | (have j0 := b3e81 X0 X1 x
               grind)
            | exact resolve b3e81 b3e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e81
          have b3e101 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b3e33 (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e33
            | exact resolve b3e33 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33
          have b3e204 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e101
               grind)
            | exact superpose b3e101 b3e22
            | exact resolve b3e22 b3e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e207 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ x) := by
            intro X0
            first
            | (have i₁ := b3e204
               have i₂ := b3e35 X0
               grind)
            | exact superpose b3e35 b3e204
            | exact resolve b3e204 b3e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e35 b3e204
          have b3e311 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ x) ∨ (σ x) = (k (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b3e82 (σ y) x (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e82
            | exact resolve b3e82 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e82
          have b3e377 : (σ x) = (k (σ y) (σ y)) := by
            first
            | (have r₁ := b3e311 x
               have r₂ := b3e207 x
               grind)
            | exact resolve b3e311 b3e207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e207 b3e311
          have b3e389 : (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b3e377
               have i₂ := b3e19 y y
               grind)
            | exact superpose b3e19 b3e377
            | exact resolve b3e377 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e377
          have b3e398 : (k y y) = (τ (σ x)) := by
            first
            | (have i₁ := b3e14 (k y y)
               have i₂ := b3e389
               grind)
            | exact superpose b3e389 b3e14
            | exact resolve b3e14 b3e389
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e389
          have b3e400 : x = (k y y) := by
            first
            | (have i₁ := b3e398
               have i₂ := b3e14 x
               grind)
            | exact superpose b3e14 b3e398
            | exact resolve b3e398 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e398
          have b3e416 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b3e18 X1 X0
               have i₂ := b3e86 X0 X0
               grind)
            | exact superpose b3e86 b3e18
            | (have j0 := b3e18 X1 X0
               have j1 := b3e86 X1 X0
               grind)
            | exact resolve b3e18 b3e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e430 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b3e16 X1 X0
               have i₂ := b3e86 X1 X0
               grind)
            | (have i₁ := b3e16 (σ x) (σ y)
               have i₂ := b3e86 X0 X1
               grind)
            | exact superpose b3e86 b3e16
            | (have j0 := b3e16 X1 X0
               have j1 := b3e86 X1 X0
               grind)
            | (have r₁ := b3e16 (M.op (σ y) (σ x)) X1
               have r₂ := b3e86 (M.op (σ y) (σ x)) X1
               grind)
            | exact resolve b3e16 b3e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e86
          have b3e444 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b3e430 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e430
          have b3e451 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b3e444 X0 X1
               have i₂ := b3e101
               grind)
            | exact superpose b3e101 b3e444
            | (have j0 := b3e444 X0 X1
               grind)
            | (have r₁ := b3e444 X0 (M.op (σ x) (σ y))
               have r₂ := b3e101
               grind)
            | exact resolve b3e444 b3e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e444
          have b3e464 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b3e416 X0 X1
               have j1 := b3e16 X1 X0
               grind)
            | (have r₁ := b3e416 X0 (σ x)
               have r₂ := b3e16 (σ x) (σ y)
               grind)
            | (have r₁ := b3e416 X0 (M.op X1 (M.op (σ y) (σ x)))
               have r₂ := b3e16 (M.op (σ y) (σ x)) X1
               grind)
            | (have r₁ := b3e416 X1 X0
               have r₂ := b3e16 X0 X1
               grind)
            | exact resolve b3e416 b3e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e416
          have b3e473 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b3e464 X0 X1
               have i₂ := b3e101
               grind)
            | exact superpose b3e101 b3e464
            | (have j0 := b3e464 X0 X1
               grind)
            | exact resolve b3e464 b3e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e101 b3e464
          have b3e478 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b3e473 X0 X1
               have j1 := b3e451 X0 X1
               grind)
            | (have r₁ := b3e473 X0 X1
               have r₂ := b3e451 X0 X1
               grind)
            | (have r₁ := b3e473 X0 (M.op (σ x) (σ y))
               have r₂ := b3e451 X0 (M.op (σ x) (σ y))
               grind)
            | (have r₁ := b3e473 (σ y) (σ x)
               have r₂ := b3e451 X0 (k (σ x) (σ y))
               grind)
            | exact resolve b3e473 b3e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e451 b3e473
          have b3e1003 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b3e478 y y
               have i₂ := b3e400
               grind)
            | exact superpose b3e400 b3e478
            | exact resolve b3e478 b3e400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e400 b3e478
          have b3e1032 : x = (M.op y y) := by grind
          clear b3e1003
          have b3e1047 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b3e13 X0 y
               have i₂ := b3e1032
               grind)
            | exact superpose b3e1032 b3e13
            | exact resolve b3e13 b3e1032
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e1053 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b3e36 X0 y
               have i₂ := b3e1032
               grind)
            | exact superpose b3e1032 b3e36
            | exact resolve b3e36 b3e1032
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e36 b3e1032
          have b3e1067 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x := by
            intro X0
            first
            | (have i₁ := b3e1053 X0
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e1053
            | exact resolve b3e1053 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1053
          have b3e1072 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
            intro X0
            first
            | (have i₁ := b3e1047 X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e1047
            | exact resolve b3e1047 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1047
          have b3e1073 : x = y := by
            first
            | (have i₁ := b3e1072 x
               have i₂ := b3e1067 x
               grind)
            | exact superpose b3e1067 b3e1072
            | exact resolve b3e1072 b3e1067
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1067 b3e1072
          have b3e1153 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e1073
               grind)
            | exact superpose b3e1073 b3e22
            | exact resolve b3e22 b3e1073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e1154 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e23
               have i₂ := b3e1073
               grind)
            | exact superpose b3e1073 b3e23
            | exact resolve b3e23 b3e1073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1073
          have b3e1183 : False := by grind
          exact b3e1183
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b4e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
              intro X0 X1
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : x = (M.op y x) := by grind
            have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b4e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e33 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
              intro X0
              first
              | (have i₁ := b4e14 X0 x
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e14
              | exact resolve b4e14 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e35 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x := by
              intro X0
              first
              | (have i₁ := b4e33 X0
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e33
              | exact resolve b4e33 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e33
            have b4e37 : x = (M.op x y) := by
              first
              | (have i₁ := b4e35 x
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e35
              | exact resolve b4e35 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e35
            have b4e44 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
            have b4e46 : (M.op x y) = (k x y) := by grind
            clear b4e44
            have b4e47 : x = (k x y) := by
              first
              | (have i₁ := b4e46
                 have i₂ := b4e37
                 grind)
              | exact superpose b4e37 b4e46
              | exact resolve b4e46 b4e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e37 b4e46
            have b4e57 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b4e60 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e57
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e57 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e57
            have b4e61 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b4e60
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e60
              | exact resolve b4e60 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e60
            have b4e62 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e61
                 have i₂ := b4e47
                 grind)
              | exact superpose b4e47 b4e61
              | exact resolve b4e61 b4e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e47 b4e61
            have b4e93 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e24
                 have i₂ := b4e62
                 grind)
              | exact superpose b4e62 b4e24
              | exact resolve b4e24 b4e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e94 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e62
                 grind)
              | exact superpose b4e62 b4e23
              | exact resolve b4e23 b4e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e62
            have b4e101 : False := by grind
            exact b4e101
          · have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : x = (M.op y x) := by grind
            have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b5e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b5e25 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e41 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
            have b5e42 : (M.op x y) = (k x y) := by grind
            clear b5e41
            have b5e46 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b5e47 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e46
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e46 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e46
            have b5e48 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b5e47
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e47
              | exact resolve b5e47 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e47
            have b5e49 : (σ (M.op x y)) = (σ y) := by
              first
              | (have i₁ := b5e48
                 have i₂ := b5e42
                 grind)
              | exact superpose b5e42 b5e48
              | exact resolve b5e48 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e42 b5e48
            have b5e52 : (M.op x y) = (τ (σ y)) := by
              first
              | (have i₁ := b5e15 (M.op x y)
                 have i₂ := b5e49
                 grind)
              | exact superpose b5e49 b5e15
              | exact resolve b5e15 b5e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e49
            have b5e53 : y = (M.op x y) := by
              first
              | (have i₁ := b5e52
                 have i₂ := b5e15 y
                 grind)
              | exact superpose b5e15 b5e52
              | exact resolve b5e52 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e52
            have b5e56 : False := by grind
            exact b5e56
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : x = (M.op y x) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b6e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e20
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e20
            | exact resolve b6e20 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e46 : x ≠ x ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b6e16 x y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 x y
               grind)
            | (have r₁ := b6e16 x y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e47 : (M.op x y) = (k x y) := by grind
          clear b6e46
          have b6e49 : y = (k x y) := by
            first
            | (have i₁ := b6e47
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e47
            | exact resolve b6e47 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e47
          have b6e66 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 X0 (σ y)
               grind)
            | (have i₁ := b6e23
               have i₂ := b6e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 X0 (σ y)
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e68 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b6e66 X0
               have j1 := b6e16 X0 (σ y)
               grind)
            | (have r₁ := b6e66 X0
               have r₂ := b6e16 X0 (σ y)
               grind)
            | exact resolve b6e66 b6e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e66
          have b6e166 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b6e68 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e68
          have b6e167 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e166
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e166
            | exact resolve b6e166 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e166
          have b6e168 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e167
               have i₂ := b6e49
               grind)
            | exact superpose b6e49 b6e167
            | exact resolve b6e167 b6e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e49 b6e167
          have b6e169 : False := by grind
          exact b6e169
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
              intro X0 X1
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b7e22 : x = (M.op y x) := by grind
            have b7e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            have b7e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e31 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e33 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x := by
              intro X0
              first
              | (have i₁ := b7e31 X0
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e31
              | exact resolve b7e31 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e31
            have b7e34 : x = (M.op x y) := by
              first
              | (have i₁ := b7e33 x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e33
              | exact resolve b7e33 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e33
            have b7e37 : x ≠ x ∨ (M.op x y) = (k x y) := by
              first
              | (have i₁ := b7e17 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 x y
                 grind)
              | (have r₁ := b7e17 x y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e42 : (M.op x y) = (k x y) := by grind
            clear b7e37
            have b7e46 : x = (k x y) := by
              first
              | (have i₁ := b7e42
                 have i₂ := b7e34
                 grind)
              | exact superpose b7e34 b7e42
              | exact resolve b7e42 b7e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e42
            have b7e63 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e24
                 have i₂ := b7e19 X0 (σ y)
                 grind)
              | (have i₁ := b7e24
                 have i₂ := b7e19 (M.op (σ y) (σ y)) x
                 grind)
              | exact superpose b7e19 b7e24
              | (have j1 := b7e19 X0 (σ y)
                 grind)
              | (have r₁ := b7e24
                 have r₂ := b7e19 (σ x) (σ y)
                 grind)
              | exact resolve b7e24 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e65 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b7e63 X0
                 have j1 := b7e17 X0 (σ y)
                 grind)
              | (have r₁ := b7e63 X0
                 have r₂ := b7e17 X0 (σ y)
                 grind)
              | exact resolve b7e63 b7e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e63
            have b7e251 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b7e65 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e65
            have b7e252 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e251
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e251
              | exact resolve b7e251 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e251
            have b7e253 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b7e252
                 have i₂ := b7e46
                 grind)
              | exact superpose b7e46 b7e252
              | exact resolve b7e252 b7e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e46 b7e252
            have b7e254 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b7e21
                 have i₂ := b7e253
                 grind)
              | exact superpose b7e253 b7e21
              | exact resolve b7e21 b7e253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e253
            have b7e259 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b7e254
                 have i₂ := b7e34
                 grind)
              | exact superpose b7e34 b7e254
              | exact resolve b7e254 b7e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e34 b7e254
            have b7e260 : False := by grind
            exact b7e260
          · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b8e22 : x = (M.op y x) := by grind
            have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e36 : x ≠ x ∨ (M.op x y) = (k x y) := by
              first
              | (have i₁ := b8e17 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 x y
                 grind)
              | (have r₁ := b8e17 x y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e39 : (M.op x y) = (k x y) := by grind
            clear b8e36
            have b8e59 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e24
                 have i₂ := b8e19 X0 (σ y)
                 grind)
              | (have i₁ := b8e24
                 have i₂ := b8e19 (M.op (σ y) (σ y)) x
                 grind)
              | exact superpose b8e19 b8e24
              | (have j1 := b8e19 X0 (σ y)
                 grind)
              | (have r₁ := b8e24
                 have r₂ := b8e19 (σ x) (σ y)
                 grind)
              | exact resolve b8e24 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e61 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b8e59 X0
                 have j1 := b8e17 X0 (σ y)
                 grind)
              | (have r₁ := b8e59 X0
                 have r₂ := b8e17 X0 (σ y)
                 grind)
              | exact resolve b8e59 b8e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e59
            have b8e155 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b8e61 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e61
            have b8e156 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e155
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e155
              | exact resolve b8e155 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155
            have b8e157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e156
                 have i₂ := b8e39
                 grind)
              | exact superpose b8e39 b8e156
              | exact resolve b8e156 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e39 b8e156
            have b8e158 : False := by grind
            exact b8e158
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : x ≠ (M.op y x) := by grind
          have b9e22 : x = (M.op y y) := by grind
          have b9e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b9e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e20
            | exact resolve b9e20 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e43 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 (σ x) (σ y)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e47 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b9e43
          have b9e49 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b9e47
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e47
            | exact resolve b9e47 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e47
          have b9e55 : y = (k x y) ∨ x = (M.op y x) := by grind
          have b9e56 : y = (k x y) := by
            first
            | (have r₁ := b9e55
               have r₂ := b9e21
               grind)
            | exact resolve b9e55 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e55
          have b9e102 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e49
               grind)
            | exact superpose b9e49 b9e26
            | exact resolve b9e26 b9e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26 b9e49
          have b9e106 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b9e102
               have i₂ := b9e56
               grind)
            | exact superpose b9e56 b9e102
            | exact resolve b9e102 b9e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e56 b9e102
          have b9e107 : False := by grind
          exact b9e107
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
              intro X0 X1
              grind
            have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : x ≠ (M.op y x) := by grind
            have b10e23 : x = (M.op y y) := by grind
            have b10e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b10e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e32 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
              intro X0
              first
              | (have i₁ := b10e14 X0 y
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e38 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e42 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b10e38
            have b10e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b10e42
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e42
              | exact resolve b10e42 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e42
            have b10e47 : y = (k x y) ∨ x = (M.op y x) := by grind
            have b10e48 : y = (k x y) := by
              first
              | (have r₁ := b10e47
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e47 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e47
            have b10e57 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e14 X1 X2
                 have i₂ := b10e19 X0 X1
                 grind)
              | (have i₁ := b10e14 X0 X1
                 have i₂ := b10e19 (M.op X0 X0) X1
                 grind)
              | exact superpose b10e19 b10e14
              | (have j1 := b10e19 X0 X1
                 grind)
              | exact resolve b10e14 b10e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e61 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X2) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1 X2
              first
              | (have j0 := b10e57 X0 X1 X2
                 have j1 := b10e17 X0 X1
                 grind)
              | (have r₁ := b10e57 (M.op (M.op X2 X2) X2) X1 X2
                 have r₂ := b10e17 (M.op (M.op X2 X2) X2) X1
                 grind)
              | (have r₁ := b10e57 X0 X1 (M.op X1 X0)
                 have r₂ := b10e17 (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))
                 grind)
              | (have r₁ := b10e57 X0 X1 X2
                 have r₂ := b10e17 X0 X1
                 grind)
              | exact resolve b10e57 b10e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e57
            have b10e72 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = (M.op x y) := by
              intro X1
              first
              | (have i₁ := b10e14 x X1
                 have i₂ := b10e32 x
                 grind)
              | exact superpose b10e32 b10e14
              | exact resolve b10e14 b10e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e281 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = X2 ∨ (k X2 X1) = (M.op X2 X1) ∨ (M.op X1 X2) = X2 ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e19 X2 X1
                 have i₂ := b10e61 X1 X1 X0
                 grind)
              | exact superpose b10e61 b10e19
              | (have j0 := b10e19 X2 X1
                 have j1 := b10e61 X2 X1 X2
                 grind)
              | exact resolve b10e19 b10e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e294 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ X2 ∨ (k X2 X1) = (M.op X2 X1) ∨ (k X2 X1) = (M.op X2 X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e17 X2 X1
                 have i₂ := b10e61 X2 X1 X0
                 grind)
              | (have i₁ := b10e17 X2 (M.op X2 X2)
                 have i₂ := b10e61 X0 X1 X2
                 grind)
              | exact superpose b10e61 b10e17
              | (have j0 := b10e17 X2 X1
                 have j1 := b10e61 X2 X1 X2
                 grind)
              | (have r₁ := b10e17 (M.op (M.op X2 X2) X2) X1
                 have r₂ := b10e61 (M.op (M.op X2 X2) X2) X1 X2
                 grind)
              | (have r₁ := b10e17 (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))
                 have r₂ := b10e61 X0 X1 (M.op X1 X0)
                 grind)
              | exact resolve b10e17 b10e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e61
            have b10e312 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ X2 ∨ (k X2 X1) = (M.op X2 X1) := by
              intro X0 X1 X2
              first
              | (have j0 := b10e294 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e294
            have b10e322 : ∀ X1 X2 : G, (M.op x y) ≠ X2 ∨ (k X2 X1) = (M.op X2 X1) := by
              intro X1 X2
              first
              | (have i₁ := b10e312 x X1 X2
                 have i₂ := b10e72 x
                 grind)
              | exact superpose b10e72 b10e312
              | (have j0 := b10e312 x X1 X2
                 grind)
              | (have r₁ := b10e312 X1 X1 (M.op x y)
                 have r₂ := b10e72 X1
                 grind)
              | exact resolve b10e312 b10e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e312
            have b10e331 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = X2 ∨ (k X2 X1) = (M.op X2 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X0 X1 X2
              first
              | (have j0 := b10e281 X0 X1 X2
                 have j1 := b10e17 X2 X1
                 grind)
              | (have r₁ := b10e281 X0 X1 X0
                 have r₂ := b10e17 X0 (M.op X0 X0)
                 grind)
              | (have r₁ := b10e281 X0 X1 (M.op X1 (M.op (M.op X0 X0) X0))
                 have r₂ := b10e17 (M.op (M.op X0 X0) X0) X1
                 grind)
              | (have r₁ := b10e281 X0 X1 X0
                 have r₂ := b10e17 X0 X1
                 grind)
              | exact resolve b10e281 b10e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e281
            have b10e346 : ∀ X1 X2 : G, (M.op x y) = X2 ∨ (k X2 X1) = (M.op X2 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X1 X2
              first
              | (have i₁ := b10e331 x X1 X2
                 have i₂ := b10e72 x
                 grind)
              | exact superpose b10e72 b10e331
              | (have j0 := b10e331 x X1 X2
                 grind)
              | exact resolve b10e331 b10e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e72 b10e331
            have b10e350 : ∀ X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X1 X2
              first
              | (have j0 := b10e346 X1 X2
                 have j1 := b10e322 X1 X2
                 grind)
              | (have r₁ := b10e346 X1 X2
                 have r₂ := b10e322 X1 X2
                 grind)
              | (have r₁ := b10e346 X1 (M.op x y)
                 have r₂ := b10e322 X1 (M.op x y)
                 grind)
              | (have r₁ := b10e346 y x
                 have r₂ := b10e322 X1 (k x y)
                 grind)
              | exact resolve b10e346 b10e322
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e322 b10e346
            have b10e722 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b10e350 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e350
            have b10e723 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b10e722 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e722
            have b10e746 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b10e20 X0 X0
                 have i₂ := b10e723 (σ X0)
                 grind)
              | exact superpose b10e723 b10e20
              | exact resolve b10e20 b10e723
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e754 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b10e746 X0
                 have i₂ := b10e723 X0
                 grind)
              | exact superpose b10e723 b10e746
              | exact resolve b10e746 b10e723
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e723 b10e746
            have b10e974 : ∀ X0 : G, (M.op x y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b10e32 (σ X0)
                 have i₂ := b10e754 X0
                 grind)
              | exact superpose b10e754 b10e32
              | exact resolve b10e32 b10e754
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32 b10e754
            have b10e1403 : (M.op x y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b10e974 x
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e974
              | exact resolve b10e974 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e1404 : (M.op x y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b10e974 y
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e974
              | exact resolve b10e974 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e974
            have b10e1415 : (M.op x y) = (σ x) := by
              first
              | (have i₁ := b10e1404
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e1404
              | exact resolve b10e1404 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1404
            have b10e1800 : (M.op x y) = (σ (k x y)) := by
              first
              | (have i₁ := b10e43
                 have i₂ := b10e1403
                 grind)
              | exact superpose b10e1403 b10e43
              | exact resolve b10e43 b10e1403
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e43 b10e1403
            have b10e1808 : (M.op x y) = (σ y) := by
              first
              | (have i₁ := b10e1800
                 have i₂ := b10e48
                 grind)
              | exact superpose b10e48 b10e1800
              | exact resolve b10e1800 b10e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e48 b10e1800
            have b10e1813 : (σ x) = (σ y) := by
              first
              | (have i₁ := b10e1808
                 have i₂ := b10e1415
                 grind)
              | exact superpose b10e1415 b10e1808
              | exact resolve b10e1808 b10e1415
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1415 b10e1808
            have b10e1910 : y = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 y
                 have i₂ := b10e1813
                 grind)
              | exact superpose b10e1813 b10e15
              | exact resolve b10e15 b10e1813
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1813
            have b10e1951 : x = y := by
              first
              | (have i₁ := b10e1910
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e1910
              | exact resolve b10e1910 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1910
            have b10e2071 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b10e22
                 have i₂ := b10e1951
                 grind)
              | exact superpose b10e1951 b10e22
              | exact resolve b10e22 b10e1951
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e2072 : x = (M.op x x) := by
              first
              | (have i₁ := b10e23
                 have i₂ := b10e1951
                 grind)
              | exact superpose b10e1951 b10e23
              | exact resolve b10e23 b10e1951
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1951
            have b10e2121 : False := by grind
            exact b10e2121
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : x ≠ (M.op y x) := by grind
            have b11e23 : x = (M.op y y) := by grind
            have b11e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b11e25 : y ≠ (M.op x y) := by grind
            have b11e26 : y ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e39 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b11e39
            have b11e42 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e41
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e41
              | exact resolve b11e41 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e41
            have b11e50 : y = (k x y) ∨ x = (M.op y x) := by grind
            have b11e51 : y = (k x y) := by
              first
              | (have r₁ := b11e50
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e50 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e50
            have b11e95 : (σ y) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b11e17 (σ y) (σ x)
                 have i₂ := b11e42
                 grind)
              | exact superpose b11e42 b11e17
              | (have j0 := b11e17 (σ y) (σ x)
                 grind)
              | exact resolve b11e17 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e42
            have b11e96 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b11e95
                 have i₂ := b11e51
                 grind)
              | exact superpose b11e51 b11e95
              | exact resolve b11e95 b11e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e51 b11e95
            have b11e97 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
            clear b11e96
            have b11e99 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
              first
              | (have i₁ := b11e97
                 have i₂ := b11e20 y x
                 grind)
              | exact superpose b11e20 b11e97
              | exact resolve b11e97 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e97
            have b11e100 : (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b11e99
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e99
              | exact resolve b11e99 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e99
            have b11e130 : (k y x) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k y x)
                 have i₂ := b11e100
                 grind)
              | exact superpose b11e100 b11e15
              | exact resolve b11e15 b11e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e100
            have b11e131 : x = (k y x) := by
              first
              | (have i₁ := b11e130
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e130
              | exact resolve b11e130 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e130
            have b11e166 : x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b11e19 y x
                 have i₂ := b11e131
                 grind)
              | exact superpose b11e131 b11e19
              | (have j0 := b11e19 y x
                 grind)
              | exact resolve b11e19 b11e131
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e131
            have b11e167 : y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b11e166
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e166 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e166
            have b11e169 : y = (M.op x y) := by
              first
              | (have r₁ := b11e167
                 have r₂ := b11e26
                 grind)
              | exact resolve b11e167 b11e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e167
            have b11e171 : False := by grind
            exact b11e171
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b12e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
              intro X0 X1
              grind
            have b12e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b12e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : x ≠ (M.op y x) := by grind
            have b12e23 : x = (M.op y y) := by grind
            have b12e25 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b12e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e21
              | exact resolve b12e21 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e34 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
              intro X0
              first
              | (have i₁ := b12e14 X0 y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e36 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
              intro X0
              first
              | (have i₁ := b12e34 X0
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e34
              | exact resolve b12e34 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e34
            have b12e37 : y = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b12e36 (σ y)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e36
              | exact resolve b12e36 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e38 : y = (M.op y x) := by
              first
              | (have i₁ := b12e36 y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e36
              | exact resolve b12e36 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = y := by
              intro X1
              first
              | (have i₁ := b12e14 x X1
                 have i₂ := b12e36 x
                 grind)
              | exact superpose b12e36 b12e14
              | exact resolve b12e14 b12e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e36
            have b12e46 : y ≠ y ∨ (M.op y x) = (k y x) := by
              first
              | (have i₁ := b12e17 y x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e17
              | (have j0 := b12e17 y x
                 grind)
              | (have r₁ := b12e17 y x
                 have r₂ := b12e26
                 grind)
              | exact resolve b12e17 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e47 : (M.op y x) = (k y x) := by grind
            clear b12e46
            have b12e48 : y = (k y x) := by
              first
              | (have i₁ := b12e47
                 have i₂ := b12e38
                 grind)
              | exact superpose b12e38 b12e47
              | exact resolve b12e47 b12e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e47
            have b12e71 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b12e77 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b12e71 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e71
            have b12e83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b12e77 X0 X1
                 have j1 := b12e17 X0 X1
                 grind)
              | (have r₁ := b12e77 X0 X1
                 have r₂ := b12e17 X0 X1
                 grind)
              | exact resolve b12e77 b12e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e77
            have b12e90 : x ≠ y := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e38
                 grind)
              | exact superpose b12e38 b12e22
              | exact resolve b12e22 b12e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e38
            have b12e116 : y = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e40 (σ y)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e40
              | exact resolve b12e40 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e139 : y ≠ (σ y) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e116
                 grind)
              | exact superpose b12e116 b12e28
              | exact resolve b12e28 b12e116
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e116
            have b12e283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e83 (σ X0) (σ X1)
                 have i₂ := b12e20 X0 X1
                 grind)
              | exact superpose b12e20 b12e83
              | exact resolve b12e83 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e83
            have b12e1447 : y = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b12e37
                 have i₂ := b12e283 y x
                 grind)
              | exact superpose b12e283 b12e37
              | (have j1 := b12e283 y x
                 grind)
              | exact resolve b12e37 b12e283
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e37 b12e283
            have b12e1489 : y = (σ y) ∨ (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b12e1447
                 have i₂ := b12e48
                 grind)
              | exact superpose b12e48 b12e1447
              | exact resolve b12e1447 b12e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1447
            have b12e1507 : (σ x) = (σ (k y x)) := by
              first
              | (have r₁ := b12e1489
                 have r₂ := b12e139
                 grind)
              | exact resolve b12e1489 b12e139
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e139 b12e1489
            have b12e1520 : (σ x) = (σ y) := by
              first
              | (have i₁ := b12e1507
                 have i₂ := b12e48
                 grind)
              | exact superpose b12e48 b12e1507
              | exact resolve b12e1507 b12e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e48 b12e1507
            have b12e1531 : x = (τ (σ y)) := by
              first
              | (have i₁ := b12e15 x
                 have i₂ := b12e1520
                 grind)
              | exact superpose b12e1520 b12e15
              | exact resolve b12e15 b12e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1520
            have b12e1568 : x = y := by
              first
              | (have i₁ := b12e1531
                 have i₂ := b12e15 y
                 grind)
              | exact superpose b12e15 b12e1531
              | exact resolve b12e1531 b12e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1531
            have b12e1577 : False := by grind
            exact b12e1577
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
                intro X0 X1
                grind
              have b13e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b13e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b13e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : x = (M.op y y) := by grind
              have b13e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 (τ X0) X1
                   have i₂ := b13e17 X0
                   grind)
                | exact superpose b13e17 b13e21
                | exact resolve b13e21 b13e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b13e16 (k (τ X0) X1)
                   have i₂ := b13e30 X0 X1
                   grind)
                | exact superpose b13e30 b13e16
                | exact resolve b13e16 b13e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e36 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 X0) X0) := by
                intro X0
                first
                | (have i₁ := b13e15 (σ y) X0
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e15
                | exact resolve b13e15 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e38 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b13e15 X0 (σ y)
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e15
                | exact resolve b13e15 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e40 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b13e15 X0 y
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e43 : (M.op x y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e38 x
                   have i₂ := b13e40 x
                   grind)
                | exact superpose b13e40 b13e38
                | exact resolve b13e38 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e38
              have b13e46 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X1 (M.op X1 X1)) = (k X1 (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e18 X1 (M.op X1 X1)
                   have i₂ := b13e15 X0 X1
                   grind)
                | exact superpose b13e15 b13e18
                | (have j0 := b13e18 X1 (M.op X1 X1)
                   grind)
                | (have r₁ := b13e18 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
                   have r₂ := b13e15 X0 (M.op X0 (M.op X0 X0))
                   grind)
                | exact resolve b13e18 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e52 : ∀ X1 : G, (M.op x y) ≠ X1 ∨ (M.op X1 (M.op X1 X1)) = (k X1 (M.op X1 X1)) := by
                intro X1
                first
                | (have i₁ := b13e46 x X1
                   have i₂ := b13e40 x
                   grind)
                | exact superpose b13e40 b13e46
                | (have j0 := b13e46 x X1
                   grind)
                | (have r₁ := b13e46 x (M.op x y)
                   have r₂ := b13e40 x
                   grind)
                | exact resolve b13e46 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e46
              have b13e54 : ∀ X1 : G, (M.op x y) ≠ X1 ∨ (M.op x y) = (k X1 (M.op X1 X1)) := by
                intro X1
                first
                | (have i₁ := b13e52 X1
                   have i₂ := b13e40 X1
                   grind)
                | exact superpose b13e40 b13e52
                | (have j0 := b13e52 X1
                   grind)
                | (have r₁ := b13e52 (M.op x (M.op x x))
                   have r₂ := b13e40 x
                   grind)
                | exact resolve b13e52 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e52
              have b13e70 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b13e72 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e15 X1 X2
                   have i₂ := b13e20 X0 X1
                   grind)
                | (have i₁ := b13e15 X0 X1
                   have i₂ := b13e20 (M.op X0 X0) X1
                   grind)
                | exact superpose b13e20 b13e15
                | (have j1 := b13e20 X0 X1
                   grind)
                | exact resolve b13e15 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e75 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b13e70 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e70
              have b13e78 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X2) ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1 X2
                first
                | (have j0 := b13e72 X0 X1 X2
                   have j1 := b13e18 X0 X1
                   grind)
                | (have r₁ := b13e72 (M.op (M.op X2 X2) X2) X1 X2
                   have r₂ := b13e18 (M.op (M.op X2 X2) X2) X1
                   grind)
                | (have r₁ := b13e72 X0 X1 (M.op X1 X0)
                   have r₂ := b13e18 (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))
                   grind)
                | (have r₁ := b13e72 X0 X1 X2
                   have r₂ := b13e18 X0 X1
                   grind)
                | exact resolve b13e72 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e72
              have b13e80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b13e75 X0 X1
                   have j1 := b13e18 X0 X1
                   grind)
                | (have r₁ := b13e75 X0 X1
                   have r₂ := b13e18 X0 X1
                   grind)
                | exact resolve b13e75 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e75
              have b13e83 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (σ x)) ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have i₁ := b13e78 X0 X1 x
                   have i₂ := b13e36 x
                   grind)
                | exact superpose b13e36 b13e78
                | (have j0 := b13e78 X0 X1 x
                   grind)
                | exact resolve b13e78 b13e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e36 b13e78
              have b13e89 : (M.op x y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b13e40 (σ y)
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e40
                | exact resolve b13e40 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e92 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = (M.op x y) := by
                intro X1
                first
                | (have i₁ := b13e15 x X1
                   have i₂ := b13e40 x
                   grind)
                | exact superpose b13e40 b13e15
                | exact resolve b13e15 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e97 : (M.op x y) ≠ (σ (M.op x y)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e43
                   grind)
                | exact superpose b13e43 b13e22
                | exact resolve b13e22 b13e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e43
              have b13e223 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b13e30 X0 X1
                   have i₂ := b13e80 (τ X0) X1
                   grind)
                | exact superpose b13e80 b13e30
                | (have j1 := b13e80 (τ X0) X1
                   grind)
                | exact resolve b13e30 b13e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30 b13e80
              have b13e229 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e35 X1 (τ X0)
                   have i₂ := b13e17 X0
                   grind)
                | exact superpose b13e17 b13e35
                | exact resolve b13e35 b13e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e35
              have b13e264 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) := by
                first
                | (have j0 := b13e54 (M.op x y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e54
              have b13e311 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e20 X1 X0
                   have i₂ := b13e83 X0 X0
                   grind)
                | exact superpose b13e83 b13e20
                | (have j0 := b13e20 X1 X0
                   have j1 := b13e83 X1 X0
                   grind)
                | exact resolve b13e20 b13e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e321 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e18 X1 X0
                   have i₂ := b13e83 X1 X0
                   grind)
                | (have i₁ := b13e18 (σ x) (σ y)
                   have i₂ := b13e83 X0 X1
                   grind)
                | exact superpose b13e83 b13e18
                | (have j0 := b13e18 X1 X0
                   have j1 := b13e83 X1 X0
                   grind)
                | (have r₁ := b13e18 (M.op (σ y) (σ x)) X1
                   have r₂ := b13e83 (M.op (σ y) (σ x)) X1
                   grind)
                | exact resolve b13e18 b13e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e83
              have b13e332 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b13e321 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e321
              have b13e341 : ∀ X0 X1 : G, (M.op x y) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e332 X0 X1
                   have i₂ := b13e89
                   grind)
                | exact superpose b13e89 b13e332
                | (have j0 := b13e332 X0 X1
                   grind)
                | (have r₁ := b13e332 X0 (M.op x y)
                   have r₂ := b13e89
                   grind)
                | exact resolve b13e332 b13e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e332
              have b13e351 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
                intro X0 X1
                first
                | (have j0 := b13e311 X0 X1
                   have j1 := b13e18 X1 X0
                   grind)
                | (have r₁ := b13e311 X0 (σ x)
                   have r₂ := b13e18 (σ x) (σ y)
                   grind)
                | (have r₁ := b13e311 X0 (M.op X1 (M.op (σ y) (σ x)))
                   have r₂ := b13e18 (M.op (σ y) (σ x)) X1
                   grind)
                | (have r₁ := b13e311 X1 X0
                   have r₂ := b13e18 X0 X1
                   grind)
                | exact resolve b13e311 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e311
              have b13e363 : ∀ X0 X1 : G, (M.op x y) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e351 X0 X1
                   have i₂ := b13e89
                   grind)
                | exact superpose b13e89 b13e351
                | (have j0 := b13e351 X0 X1
                   grind)
                | exact resolve b13e351 b13e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e89 b13e351
              have b13e371 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
                intro X0 X1
                first
                | (have j0 := b13e363 X0 X1
                   have j1 := b13e341 X0 X1
                   grind)
                | (have r₁ := b13e363 X0 X1
                   have r₂ := b13e341 X0 X1
                   grind)
                | (have r₁ := b13e363 X0 (M.op x y)
                   have r₂ := b13e341 X0 (M.op x y)
                   grind)
                | (have r₁ := b13e363 y x
                   have r₂ := b13e341 X0 (k x y)
                   grind)
                | exact resolve b13e363 b13e341
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e341 b13e363
              have b13e1066 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b13e371 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e371
              have b13e1067 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b13e1066 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1066
              have b13e1094 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e229 X0 X0
                   have i₂ := b13e1067 (τ X0)
                   grind)
                | exact superpose b13e1067 b13e229
                | exact resolve b13e229 b13e1067
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e1103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e1094 X0
                   have i₂ := b13e1067 X0
                   grind)
                | exact superpose b13e1067 b13e1094
                | exact resolve b13e1094 b13e1067
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1067 b13e1094
              have b13e1213 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b13e92 (τ X0)
                   have i₂ := b13e1103 X0
                   grind)
                | exact superpose b13e1103 b13e92
                | exact resolve b13e92 b13e1103
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e92
              have b13e2246 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b13e223 X0 (M.op (τ X0) (τ X0))
                   have i₂ := b13e40 (τ X0)
                   grind)
                | exact superpose b13e40 b13e223
                | (have j0 := b13e223 X0 (M.op (τ X0) (τ X0))
                   grind)
                | exact resolve b13e223 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e40 b13e223
              have b13e2284 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b13e2246 X0
                   have i₂ := b13e1103 X0
                   grind)
                | exact superpose b13e1103 b13e2246
                | (have j0 := b13e2246 X0
                   grind)
                | exact resolve b13e2246 b13e1103
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2246
              have b13e2293 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b13e2284 X0
                   have i₂ := b13e17 (M.op X0 X0)
                   grind)
                | exact superpose b13e17 b13e2284
                | (have j0 := b13e2284 X0
                   grind)
                | exact resolve b13e2284 b13e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2284
              have b13e2298 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (M.op X0 X0))) ∨ (σ (M.op x y)) = (k X0 (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e2293 X0
                   have i₂ := b13e1103 X0
                   grind)
                | exact superpose b13e1103 b13e2293
                | (have j0 := b13e2293 X0
                   grind)
                | exact resolve b13e2293 b13e1103
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2293
              have b13e2302 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op X0 X0))) ∨ (σ (M.op x y)) = (k X0 (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e2298 X0
                   have i₂ := b13e229 (M.op X0 X0) X0
                   grind)
                | exact superpose b13e229 b13e2298
                | (have j0 := b13e2298 X0
                   grind)
                | exact resolve b13e2298 b13e229
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e229 b13e2298
              have b13e113333 : (τ (M.op x y)) = (τ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
                first
                | (have i₁ := b13e2302 (M.op x y)
                   have i₂ := b13e264
                   grind)
                | exact superpose b13e264 b13e2302
                | exact resolve b13e2302 b13e264
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e264 b13e2302
              have b13e113432 : (τ (M.op x y)) = (τ (M.op (M.op x y) (M.op x y))) := by
                first
                | (have r₁ := b13e113333
                   have r₂ := b13e97
                   grind)
                | exact resolve b13e113333 b13e97
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e113333
              have b13e113455 : (M.op x y) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
                first
                | (have i₁ := b13e1213 (M.op x y)
                   have i₂ := b13e113432
                   grind)
                | exact superpose b13e113432 b13e1213
                | exact resolve b13e1213 b13e113432
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1213
              have b13e113463 : (M.op (M.op x y) (M.op x y)) = (σ (τ (M.op x y))) := by
                first
                | (have i₁ := b13e17 (M.op (M.op x y) (M.op x y))
                   have i₂ := b13e113432
                   grind)
                | exact superpose b13e113432 b13e17
                | exact resolve b13e17 b13e113432
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e113432
              have b13e113491 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
                first
                | (have i₁ := b13e113463
                   have i₂ := b13e17 (M.op x y)
                   grind)
                | exact superpose b13e17 b13e113463
                | exact resolve b13e113463 b13e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e113463
              have b13e113496 : (M.op x y) = (τ (M.op (M.op x y) (M.op x y))) := by
                first
                | (have i₁ := b13e113455
                   have i₂ := b13e1103 (M.op x y)
                   grind)
                | exact superpose b13e1103 b13e113455
                | exact resolve b13e113455 b13e1103
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1103 b13e113455
              have b13e113505 : (M.op x y) = (τ (M.op x y)) := by
                first
                | (have i₁ := b13e113496
                   have i₂ := b13e113491
                   grind)
                | exact superpose b13e113491 b13e113496
                | exact resolve b13e113496 b13e113491
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e113491 b13e113496
              have b13e114194 : (M.op x y) = (σ (M.op x y)) := by
                first
                | (have i₁ := b13e17 (M.op x y)
                   have i₂ := b13e113505
                   grind)
                | exact superpose b13e113505 b13e17
                | exact resolve b13e17 b13e113505
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e113505
              have b13e114340 : False := by grind
              exact b13e114340
            · have b14e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
                intro X0 X1
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e23 : x ≠ (M.op y x) := by grind
              have b14e24 : x = (M.op y y) := by grind
              have b14e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              have b14e27 : y ≠ (M.op x y) := by grind
              have b14e28 : y ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e38 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e15 X0 (σ y)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e39 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b14e15 X0 y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e41 : (M.op x y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e38 x
                   have i₂ := b14e39 x
                   grind)
                | exact superpose b14e39 b14e38
                | exact resolve b14e38 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e38
              have b14e42 : (M.op x y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b14e39 (σ y)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e39
                | exact resolve b14e39 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e43 : (M.op x y) = (M.op y x) := by
                first
                | (have i₁ := b14e39 y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e39
                | exact resolve b14e39 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39
              have b14e60 : x ≠ (M.op x y) := by
                first
                | (have i₁ := b14e23
                   have i₂ := b14e43
                   grind)
                | exact superpose b14e43 b14e23
                | exact resolve b14e23 b14e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e74 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b14e80 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b14e74 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e74
              have b14e86 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e80 X0 X1
                   have j1 := b14e18 X0 X1
                   grind)
                | (have r₁ := b14e80 X0 X1
                   have r₂ := b14e18 X0 X1
                   grind)
                | exact resolve b14e80 b14e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e80
              have b14e93 : (M.op x y) ≠ (σ (M.op x y)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e41
                   grind)
                | exact superpose b14e41 b14e22
                | exact resolve b14e22 b14e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e41
              have b14e217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e86 (σ X0) (σ X1)
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e86
                | exact resolve b14e86 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e86
              have b14e1272 : (M.op x y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b14e42
                   have i₂ := b14e217 y x
                   grind)
                | exact superpose b14e217 b14e42
                | (have j1 := b14e217 y x
                   grind)
                | exact resolve b14e42 b14e217
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e42 b14e217
              have b14e6643 : (M.op x y) = (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b14e1272
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e1272
                | (have j1 := b14e20 y x
                   grind)
                | exact resolve b14e1272 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1272
              have b14e6732 : (M.op x y) = (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b14e6643
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e6643 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6643
              have b14e6744 : (M.op x y) = (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) := by
                first
                | (have r₁ := b14e6732
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e6732 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6732
              have b14e6753 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (σ (M.op y x)) := by
                first
                | (have i₁ := b14e6744
                   have i₂ := b14e43
                   grind)
                | exact superpose b14e43 b14e6744
                | exact resolve b14e6744 b14e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6744
              have b14e6755 : (σ x) = (σ (M.op y x)) := by
                first
                | (have r₁ := b14e6753
                   have r₂ := b14e93
                   grind)
                | exact resolve b14e6753 b14e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e93 b14e6753
              have b14e6757 : (σ (M.op x y)) = (σ x) := by
                first
                | (have i₁ := b14e6755
                   have i₂ := b14e43
                   grind)
                | exact superpose b14e43 b14e6755
                | exact resolve b14e6755 b14e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e43 b14e6755
              have b14e7327 : (M.op x y) = (τ (σ x)) := by
                first
                | (have i₁ := b14e16 (M.op x y)
                   have i₂ := b14e6757
                   grind)
                | exact superpose b14e6757 b14e16
                | exact resolve b14e16 b14e6757
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6757
              have b14e7400 : x = (M.op x y) := by
                first
                | (have i₁ := b14e7327
                   have i₂ := b14e16 x
                   grind)
                | exact superpose b14e16 b14e7327
                | exact resolve b14e7327 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7327
              have b14e7401 : False := by grind
              exact b14e7401
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b15e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e22 : x ≠ (M.op y x) := by grind
            have b15e23 : x = (M.op y y) := by grind
            have b15e25 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            have b15e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e21
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e21
              | exact resolve b15e21 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e50 : y = (k x y) ∨ x = (M.op y x) := by grind
            have b15e51 : y = (k x y) := by
              first
              | (have r₁ := b15e50
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e50 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e50
            have b15e64 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e19 X0 (σ y)
                 grind)
              | (have i₁ := b15e25
                 have i₂ := b15e19 (M.op (σ y) (σ y)) x
                 grind)
              | exact superpose b15e19 b15e25
              | (have j1 := b15e19 X0 (σ y)
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ x) (σ y)
                 grind)
              | exact resolve b15e25 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e66 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b15e64 X0
                 have j1 := b15e17 X0 (σ y)
                 grind)
              | (have r₁ := b15e64 X0
                 have r₂ := b15e17 X0 (σ y)
                 grind)
              | exact resolve b15e64 b15e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e64
            have b15e252 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b15e66 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e66
            have b15e253 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e252
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e252
              | exact resolve b15e252 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e252
            have b15e254 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e253
                 have i₂ := b15e51
                 grind)
              | exact superpose b15e51 b15e253
              | exact resolve b15e253 b15e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e51 b15e253
            have b15e255 : False := by grind
            exact b15e255
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b16e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e23 : x ≠ (M.op y x) := by grind
              have b16e24 : x = (M.op y y) := by grind
              have b16e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b16e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              have b16e27 : y ≠ (M.op x y) := by grind
              have b16e28 : y = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e49 : x = (k y x) ∨ y = (M.op x y) := by grind
              have b16e50 : y = (k x y) ∨ x = (M.op y x) := by grind
              have b16e51 : y = (k x y) := by
                first
                | (have r₁ := b16e50
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e50 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e50
              have b16e52 : x = (k y x) := by
                first
                | (have r₁ := b16e49
                   have r₂ := b16e27
                   grind)
                | exact resolve b16e49 b16e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e49
              have b16e63 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b16e26
                   have i₂ := b16e20 X0 (σ y)
                   grind)
                | (have i₁ := b16e26
                   have i₂ := b16e20 (M.op (σ y) (σ y)) x
                   grind)
                | exact superpose b16e20 b16e26
                | (have j1 := b16e20 X0 (σ y)
                   grind)
                | (have r₁ := b16e26
                   have r₂ := b16e20 (σ x) (σ y)
                   grind)
                | exact resolve b16e26 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e65 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have j0 := b16e63 X0
                   have j1 := b16e18 X0 (σ y)
                   grind)
                | (have r₁ := b16e63 X0
                   have r₂ := b16e18 X0 (σ y)
                   grind)
                | exact resolve b16e63 b16e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e63
              have b16e228 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b16e65 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e65
              have b16e229 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b16e228
                   have i₂ := b16e21 x y
                   grind)
                | exact superpose b16e21 b16e228
                | exact resolve b16e228 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e228
              have b16e230 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b16e229
                   have i₂ := b16e51
                   grind)
                | exact superpose b16e51 b16e229
                | exact resolve b16e229 b16e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e51 b16e229
              have b16e233 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b16e18 (σ y) (σ x)
                   have i₂ := b16e230
                   grind)
                | exact superpose b16e230 b16e18
                | (have j0 := b16e18 (σ y) (σ x)
                   grind)
                | (have r₁ := b16e18 (σ y) (σ x)
                   have r₂ := b16e230
                   grind)
                | exact resolve b16e18 b16e230
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e230
              have b16e234 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
              clear b16e233
              have b16e236 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
                first
                | (have i₁ := b16e234
                   have i₂ := b16e21 y x
                   grind)
                | exact superpose b16e21 b16e234
                | exact resolve b16e234 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e234
              have b16e238 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e236
                   have i₂ := b16e52
                   grind)
                | exact superpose b16e52 b16e236
                | exact resolve b16e236 b16e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e52 b16e236
              have b16e239 : False := by grind
              exact b16e239
            · have b17e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
                intro X0 X1
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : x ≠ (M.op y x) := by grind
              have b17e24 : x = (M.op y y) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e37 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b17e15 X0 y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e39 : (M.op x y) = (M.op y x) := by
                first
                | (have i₁ := b17e37 y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e37
                | exact resolve b17e37 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e51 : x ≠ (M.op x y) := by
                first
                | (have i₁ := b17e23
                   have i₂ := b17e39
                   grind)
                | exact superpose b17e39 b17e23
                | exact resolve b17e23 b17e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e39
              have b17e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X0 X1
                   have i₂ := b17e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 X2
                   have i₂ := b17e20 X0 X2
                   grind)
                | (have i₁ := b17e15 X0 X1
                   have i₂ := b17e20 (M.op X1 X1) X1
                   grind)
                | exact superpose b17e20 b17e15
                | (have j1 := b17e20 X0 X2
                   grind)
                | exact resolve b17e15 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e71 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
                intro X0 X1 X2
                first
                | (have j0 := b17e63 X0 X1 X2
                   have j1 := b17e18 X0 X2
                   grind)
                | (have r₁ := b17e63 X1 X1 X1
                   have r₂ := b17e18 (M.op X1 X1) X1
                   grind)
                | (have r₁ := b17e63 X1 X1 (M.op X1 (M.op X1 X1))
                   have r₂ := b17e18 (M.op X1 (M.op X1 X1)) X1
                   grind)
                | (have r₁ := b17e63 X0 X1 X1
                   have r₂ := b17e18 X0 X1
                   grind)
                | exact resolve b17e63 b17e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e63
              have b17e76 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op x y) = (M.op X0 X2) := by
                intro X0 X2
                first
                | (have i₁ := b17e71 X0 x X2
                   have i₂ := b17e37 x
                   grind)
                | exact superpose b17e37 b17e71
                | (have j0 := b17e71 X0 x X2
                   grind)
                | exact resolve b17e71 b17e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37 b17e71
              have b17e328 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e58 y y
                   grind)
                | exact superpose b17e58 b17e26
                | (have j1 := b17e58 y y
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e58 x y
                   grind)
                | exact resolve b17e26 b17e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58
              have b17e381 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b17e328
              have b17e753 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b17e381
                   have i₂ := b17e76 y y
                   grind)
                | exact superpose b17e76 b17e381
                | (have j1 := b17e76 y y
                   grind)
                | exact resolve b17e381 b17e76
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e381
              have b17e764 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b17e753
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e753
                | exact resolve b17e753 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e753
              have b17e765 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
              clear b17e764
              have b17e775 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b17e765
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e765
                | exact resolve b17e765 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e765
              have b17e777 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have r₁ := b17e775
                   have r₂ := b17e51
                   grind)
                | exact resolve b17e775 b17e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e775
              have b17e782 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e777
                   grind)
                | exact superpose b17e777 b17e26
                | exact resolve b17e26 b17e777
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e795 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
                first
                | (have i₁ := b17e18 (σ y) (σ y)
                   have i₂ := b17e777
                   grind)
                | exact superpose b17e777 b17e18
                | (have r₁ := b17e18 (σ y) (σ y)
                   have r₂ := b17e777
                   grind)
                | exact resolve b17e18 b17e777
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e777
              have b17e796 : (σ y) = (k (σ y) (σ y)) := by grind
              clear b17e795
              have b17e799 : (σ y) = (σ (k y y)) := by
                first
                | (have i₁ := b17e796
                   have i₂ := b17e21 y y
                   grind)
                | exact superpose b17e21 b17e796
                | exact resolve b17e796 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e796
              have b17e1358 : (σ y) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b17e799
                   have i₂ := b17e76 y y
                   grind)
                | exact superpose b17e76 b17e799
                | (have j1 := b17e76 y y
                   grind)
                | exact resolve b17e799 b17e76
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e76 b17e799
              have b17e1414 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b17e1358
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e1358
                | exact resolve b17e1358 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1358
              have b17e1422 : (M.op x y) = (M.op y y) := by
                first
                | (have r₁ := b17e1414
                   have r₂ := b17e782
                   grind)
                | exact resolve b17e1414 b17e782
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e782 b17e1414
              have b17e1428 : x = (M.op x y) := by
                first
                | (have i₁ := b17e1422
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e1422
                | exact resolve b17e1422 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1422
              have b17e1432 : False := by grind
              exact b17e1432
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b18e21 : x ≠ (M.op y x) := by grind
          have b18e22 : x ≠ (M.op y y) := by grind
          have b18e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b18e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e20
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e20
            | exact resolve b18e20 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e45 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b18e16 (σ x) (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e16
            | (have j0 := b18e16 (σ x) (σ y)
               grind)
            | (have r₁ := b18e16 (σ x) (σ y)
               have r₂ := b18e23
               grind)
            | exact resolve b18e16 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e48 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b18e45
          have b18e49 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e48
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e48
            | exact resolve b18e48 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e48
          have b18e52 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b18e26
               have i₂ := b18e49
               grind)
            | exact superpose b18e49 b18e26
            | exact resolve b18e26 b18e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e26 b18e49
          have b18e71 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b18e52
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e52
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e52 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e52
          have b18e72 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b18e71
               have r₂ := b18e22
               grind)
            | exact resolve b18e71 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e71
          have b18e73 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have r₁ := b18e72
               have r₂ := b18e21
               grind)
            | exact resolve b18e72 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e72
          have b18e74 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b18e73
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e73
            | exact resolve b18e73 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e73
          have b18e75 : False := by grind
          exact b18e75
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b19e22 : x ≠ (M.op y x) := by grind
            have b19e23 : x ≠ (M.op y y) := by grind
            have b19e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e39 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b19e17 (σ x) (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e17
              | (have j0 := b19e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b19e17 (σ x) (σ y)
                 have r₂ := b19e24
                 grind)
              | exact resolve b19e17 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b19e39
            have b19e42 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b19e41
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e41
              | exact resolve b19e41 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e41
            have b19e108 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b19e21
                 have i₂ := b19e42
                 grind)
              | exact superpose b19e42 b19e21
              | exact resolve b19e21 b19e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e42
            have b19e112 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b19e108
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e108
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e108 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e108
            have b19e113 : x = (M.op y y) ∨ x = (M.op y x) := by grind
            clear b19e112
            have b19e114 : x = (M.op y x) := by
              first
              | (have r₁ := b19e113
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e113 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e113
            have b19e115 : False := by grind
            exact b19e115
          · have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b20e22 : x ≠ (M.op y x) := by grind
            have b20e23 : x ≠ (M.op y y) := by grind
            have b20e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e36 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b20e17 (σ x) (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e39 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b20e36
            have b20e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b20e39
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e39
              | exact resolve b20e39 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e39
            have b20e51 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b20e21
                 have i₂ := b20e40
                 grind)
              | exact superpose b20e40 b20e21
              | exact resolve b20e21 b20e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e40
            have b20e71 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b20e51
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e51
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e51 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e51
            have b20e72 : x = (M.op y y) ∨ x = (M.op y x) := by grind
            clear b20e71
            have b20e73 : x = (M.op y x) := by
              first
              | (have r₁ := b20e72
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e72 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e72
            have b20e74 : False := by grind
            exact b20e74
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b21e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
              intro X0 X1
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : x ≠ (M.op y x) := by grind
            have b21e23 : x ≠ (M.op y y) := by grind
            have b21e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ x) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e31 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b21e14 (σ y) X0
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e14
              | exact resolve b21e14 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e62 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b21e63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 X1 X2
                 have i₂ := b21e19 X0 X2
                 grind)
              | (have i₁ := b21e14 X0 X1
                 have i₂ := b21e19 (M.op X1 X1) X1
                 grind)
              | exact superpose b21e19 b21e14
              | (have j1 := b21e19 X0 X2
                 grind)
              | exact resolve b21e14 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e67 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b21e62 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e62
            have b21e71 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
              intro X0 X1 X2
              first
              | (have j0 := b21e63 X0 X1 X2
                 have j1 := b21e17 X0 X2
                 grind)
              | (have r₁ := b21e63 X1 X1 X1
                 have r₂ := b21e17 (M.op X1 X1) X1
                 grind)
              | (have r₁ := b21e63 X1 X1 (M.op X1 (M.op X1 X1))
                 have r₂ := b21e17 (M.op X1 (M.op X1 X1)) X1
                 grind)
              | (have r₁ := b21e63 X0 X1 X1
                 have r₂ := b21e17 X0 X1
                 grind)
              | exact resolve b21e63 b21e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e63
            have b21e72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b21e67 X0 X1
                 have j1 := b21e17 X0 X1
                 grind)
              | (have r₁ := b21e67 X0 X1
                 have r₂ := b21e17 X0 X1
                 grind)
              | exact resolve b21e67 b21e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e67
            have b21e110 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ x)) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 x
                 have i₂ := b21e31 x
                 grind)
              | exact superpose b21e31 b21e14
              | exact resolve b21e14 b21e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e31
            have b21e272 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ x) := by
              intro X0
              first
              | (have i₁ := b21e24
                 have i₂ := b21e110 X0
                 grind)
              | exact superpose b21e110 b21e24
              | exact resolve b21e24 b21e110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e110
            have b21e311 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ x) ∨ (σ x) = (k (σ y) (σ y)) := by
              intro X0
              first
              | (have i₁ := b21e71 (σ y) x (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e71
              | exact resolve b21e71 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e71
            have b21e376 : (σ x) = (k (σ y) (σ y)) := by
              first
              | (have r₁ := b21e311 x
                 have r₂ := b21e272 x
                 grind)
              | exact resolve b21e311 b21e272
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e272 b21e311
            have b21e382 : (σ x) = (σ (k y y)) := by
              first
              | (have i₁ := b21e376
                 have i₂ := b21e20 y y
                 grind)
              | exact superpose b21e20 b21e376
              | exact resolve b21e376 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e376
            have b21e390 : (k y y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k y y)
                 have i₂ := b21e382
                 grind)
              | exact superpose b21e382 b21e15
              | exact resolve b21e15 b21e382
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e382
            have b21e392 : x = (k y y) := by
              first
              | (have i₁ := b21e390
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e390
              | exact resolve b21e390 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e390
            have b21e446 : x = (M.op y y) ∨ x = y := by
              first
              | (have i₁ := b21e72 y y
                 have i₂ := b21e392
                 grind)
              | exact superpose b21e392 b21e72
              | exact resolve b21e72 b21e392
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e72
            have b21e447 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b21e19 y y
                 have i₂ := b21e392
                 grind)
              | exact superpose b21e392 b21e19
              | (have j0 := b21e19 y y
                 grind)
              | exact resolve b21e19 b21e392
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e392
            have b21e448 : x = (M.op y y) ∨ y = (M.op y y) := by grind
            clear b21e447
            have b21e450 : y = (M.op y y) := by
              first
              | (have r₁ := b21e448
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e448 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e448
            have b21e451 : x = y := by
              first
              | (have r₁ := b21e446
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e446 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e446
            have b21e510 : y ≠ (M.op y y) := by
              first
              | (have i₁ := b21e22
                 have i₂ := b21e451
                 grind)
              | exact superpose b21e451 b21e22
              | exact resolve b21e22 b21e451
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e451
            have b21e532 : False := by grind
            exact b21e532
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : x ≠ (M.op y x) := by grind
              have b22e24 : x ≠ (M.op y y) := by grind
              have b22e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b22e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              have b22e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e66 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              have b22e69 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e66
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e66 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e66
              have b22e70 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b22e69
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e69
                | exact resolve b22e69 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e69
              have b22e102 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e70
                   grind)
                | exact superpose b22e70 b22e16
                | exact resolve b22e16 b22e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e70
              have b22e103 : y = (k x y) := by
                first
                | (have i₁ := b22e102
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e102
                | exact resolve b22e102 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e102
              have b22e109 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e103
                   grind)
                | exact superpose b22e103 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e103
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e103
              have b22e110 : x = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b22e109
                   have r₂ := b22e27
                   grind)
                | exact resolve b22e109 b22e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e109
              have b22e112 : x = (M.op y x) := by
                first
                | (have r₁ := b22e110
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e110 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e110
              have b22e114 : False := by grind
              exact b22e114
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : x ≠ (M.op y x) := by grind
              have b23e24 : x ≠ (M.op y y) := by grind
              have b23e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              have b23e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e62 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              have b23e67 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e62
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e62 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e62
              have b23e70 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e67
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e67
                | exact resolve b23e67 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e67
              have b23e74 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e70
                   grind)
                | exact superpose b23e70 b23e16
                | exact resolve b23e16 b23e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e70
              have b23e75 : y = (k x y) := by
                first
                | (have i₁ := b23e74
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e74
                | exact resolve b23e74 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e74
              have b23e105 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e75
                   grind)
                | exact superpose b23e75 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e75
              have b23e106 : x = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b23e105
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e105 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e105
              have b23e108 : x = (M.op y x) := by
                first
                | (have r₁ := b23e106
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e106 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e106
              have b23e110 : False := by grind
              exact b23e110
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b24e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e25 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            have b24e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e21
              | exact resolve b24e21 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e56 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b24e60 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e25
                 have i₂ := b24e19 X0 (σ y)
                 grind)
              | (have i₁ := b24e25
                 have i₂ := b24e19 (M.op (σ y) (σ y)) x
                 grind)
              | exact superpose b24e19 b24e25
              | (have j1 := b24e19 X0 (σ y)
                 grind)
              | (have r₁ := b24e25
                 have r₂ := b24e19 (σ x) (σ y)
                 grind)
              | exact resolve b24e25 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e61 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b24e56 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e56
            have b24e62 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b24e60 X0
                 have j1 := b24e17 X0 (σ y)
                 grind)
              | (have r₁ := b24e60 X0
                 have r₂ := b24e17 X0 (σ y)
                 grind)
              | exact resolve b24e60 b24e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e60
            have b24e66 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b24e61 X0 X1
                 have j1 := b24e17 X0 X1
                 grind)
              | (have r₁ := b24e61 X0 X1
                 have r₂ := b24e17 X0 X1
                 grind)
              | exact resolve b24e61 b24e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e61
            have b24e142 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b24e66 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e66
            have b24e146 : y ≠ y ∨ y = (k x y) := by
              first
              | (have i₁ := b24e142 x y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e142
              | (have j0 := b24e142 x y
                 grind)
              | (have r₁ := b24e142 x y
                 have r₂ := b24e26
                 grind)
              | exact resolve b24e142 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e142
            have b24e154 : y = (k x y) := by grind
            clear b24e146
            have b24e156 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b24e62 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e62
            have b24e157 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e156
                 have i₂ := b24e20 x y
                 grind)
              | exact superpose b24e20 b24e156
              | exact resolve b24e156 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e156
            have b24e158 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e157
                 have i₂ := b24e154
                 grind)
              | exact superpose b24e154 b24e157
              | exact resolve b24e157 b24e154
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e154 b24e157
            have b24e159 : False := by grind
            exact b24e159
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X1) := by
                intro X0 X1
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : x ≠ (M.op y x) := by grind
              have b25e24 : x ≠ (M.op y y) := by grind
              have b25e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b25e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              have b25e27 : y ≠ (M.op x y) := by grind
              have b25e28 : y = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e37 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
                intro X0
                first
                | (have i₁ := b25e15 X0 x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 x
                   have i₂ := b25e15 X1 x
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : (M.op x y) = (M.op y x) := by
                first
                | (have i₁ := b25e37 x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e37
                | exact resolve b25e37 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e59 : x = (k y x) ∨ y = (M.op x y) := by grind
              have b25e60 : x = (k y x) := by
                first
                | (have r₁ := b25e59
                   have r₂ := b25e27
                   grind)
                | exact resolve b25e59 b25e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e59
              have b25e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X0 X1
                   have i₂ := b25e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e72 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b25e26
                   have i₂ := b25e20 X0 (σ y)
                   grind)
                | (have i₁ := b25e26
                   have i₂ := b25e20 (M.op (σ y) (σ y)) x
                   grind)
                | exact superpose b25e20 b25e26
                | (have j1 := b25e20 X0 (σ y)
                   grind)
                | (have r₁ := b25e26
                   have r₂ := b25e20 (σ x) (σ y)
                   grind)
                | exact resolve b25e26 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e74 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have j0 := b25e72 X0
                   have j1 := b25e18 X0 (σ y)
                   grind)
                | (have r₁ := b25e72 X0
                   have r₂ := b25e18 X0 (σ y)
                   grind)
                | exact resolve b25e72 b25e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e72
              have b25e235 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b25e74 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e74
              have b25e236 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b25e235
                   have i₂ := b25e21 x y
                   grind)
                | exact superpose b25e21 b25e235
                | exact resolve b25e235 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e235
              have b25e276 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e236
                   grind)
                | exact superpose b25e236 b25e22
                | exact resolve b25e22 b25e236
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e278 : (σ y) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b25e18 (σ y) (σ x)
                   have i₂ := b25e236
                   grind)
                | exact superpose b25e236 b25e18
                | (have j0 := b25e18 (σ y) (σ x)
                   grind)
                | exact resolve b25e18 b25e236
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e279 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e278
                   have i₂ := b25e21 y x
                   grind)
                | exact superpose b25e21 b25e278
                | exact resolve b25e278 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e278
              have b25e281 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e279
                   have i₂ := b25e60
                   grind)
                | exact superpose b25e60 b25e279
                | exact resolve b25e279 b25e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e279
              have b25e282 : (σ y) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b25e281
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e281 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e281
              have b25e365 : (σ x) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e25
                   have i₂ := b25e64 y x
                   grind)
                | exact superpose b25e64 b25e25
                | (have j1 := b25e64 y x
                   grind)
                | (have r₁ := b25e25
                   have r₂ := b25e64 x y
                   grind)
                | exact resolve b25e25 b25e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e64
              have b25e461 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e365
                   have i₂ := b25e60
                   grind)
                | exact superpose b25e60 b25e365
                | exact resolve b25e365 b25e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e60 b25e365
              have b25e462 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
              clear b25e461
              have b25e487 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b25e462
                   have i₂ := b25e236
                   grind)
                | exact superpose b25e236 b25e462
                | exact resolve b25e462 b25e236
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e462
              have b25e489 : (σ y) = (M.op (σ x) (σ x)) := by
                first
                | (have r₁ := b25e487
                   have r₂ := b25e282
                   grind)
                | exact resolve b25e487 b25e282
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e282 b25e487
              have b25e504 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b25e38 X0 (σ x)
                   have i₂ := b25e489
                   grind)
                | exact superpose b25e489 b25e38
                | exact resolve b25e38 b25e489
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38 b25e489
              have b25e516 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (k x y)) := by
                intro X0
                first
                | (have i₁ := b25e504 X0
                   have i₂ := b25e236
                   grind)
                | exact superpose b25e236 b25e504
                | exact resolve b25e504 b25e236
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e236 b25e504
              have b25e528 : (M.op y x) = (σ (k x y)) := by
                first
                | (have i₁ := b25e516 x
                   have i₂ := b25e37 x
                   grind)
                | exact superpose b25e37 b25e516
                | exact resolve b25e516 b25e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37 b25e516
              have b25e533 : (M.op x y) = (σ (k x y)) := by
                first
                | (have i₁ := b25e528
                   have i₂ := b25e39
                   grind)
                | exact superpose b25e39 b25e528
                | exact resolve b25e528 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39 b25e528
              have b25e632 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b25e533
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e533
                | (have j1 := b25e20 x y
                   grind)
                | exact resolve b25e533 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e634 : (k x y) = (τ (M.op x y)) := by
                first
                | (have i₁ := b25e16 (k x y)
                   have i₂ := b25e533
                   grind)
                | exact superpose b25e533 b25e16
                | exact resolve b25e16 b25e533
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e533
              have b25e646 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b25e632
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e632 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e632
              have b25e647 : (M.op x y) = (σ (M.op x y)) := by
                first
                | (have r₁ := b25e646
                   have r₂ := b25e23
                   grind)
                | exact resolve b25e646 b25e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e646
              have b25e799 : (M.op x y) = (τ (M.op x y)) := by
                first
                | (have i₁ := b25e16 (M.op x y)
                   have i₂ := b25e647
                   grind)
                | exact superpose b25e647 b25e16
                | exact resolve b25e16 b25e647
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e647
              have b25e832 : (M.op x y) = (k x y) := by
                first
                | (have i₁ := b25e634
                   have i₂ := b25e799
                   grind)
                | exact superpose b25e799 b25e634
                | exact resolve b25e634 b25e799
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e634 b25e799
              have b25e867 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
                first
                | (have i₁ := b25e276
                   have i₂ := b25e832
                   grind)
                | exact superpose b25e832 b25e276
                | exact resolve b25e276 b25e832
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e276 b25e832
              have b25e879 : False := by grind
              exact b25e879
            · have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : x ≠ (M.op y x) := by grind
              have b26e24 : x ≠ (M.op y y) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e83 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 X0 (σ y)
                   grind)
                | (have i₁ := b26e26
                   have i₂ := b26e20 (M.op (σ y) (σ y)) x
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) (σ y)
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e85 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have j0 := b26e83 X0
                   have j1 := b26e18 X0 (σ y)
                   grind)
                | (have r₁ := b26e83 X0
                   have r₂ := b26e18 X0 (σ y)
                   grind)
                | exact resolve b26e83 b26e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e83
              have b26e153 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b26e85 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e85
              have b26e154 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e153
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e153
                | exact resolve b26e153 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e153
              have b26e155 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e154
                   grind)
                | exact superpose b26e154 b26e22
                | exact resolve b26e22 b26e154
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e154
              have b26e162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e155
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e155
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e155 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e155
              have b26e163 : x = (M.op y y) ∨ x = (M.op y x) := by grind
              clear b26e162
              have b26e165 : x = (M.op y x) := by
                first
                | (have r₁ := b26e163
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e163 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e163
              have b26e166 : False := by grind
              exact b26e166

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation4393 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
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
          have b4e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e62 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = y := by
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
          have b4e785 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e58 x y
               grind)
            | exact superpose b4e58 b4e20
            | (have j1 := b4e58 x y
               grind)
            | exact resolve b4e20 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58
          have b4e803 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e785
               have r₂ := b4e23
               grind)
            | exact resolve b4e785 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e785
          have b4e808 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e803
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e803
            | exact resolve b4e803 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e803
          have b4e1178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e808
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e808
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e808
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e808
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e808 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e808
          have b4e1179 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e1178
          have b4e1180 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e1179
               have r₂ := b4e21
               grind)
            | exact resolve b4e1179 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1179
          have b4e2695 : y = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e62 (σ x) y
               have i₂ := b4e1180
               grind)
            | exact superpose b4e1180 b4e62
            | exact resolve b4e62 b4e1180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3068 : y = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1180
               have i₂ := b4e2695
               grind)
            | exact superpose b4e2695 b4e1180
            | exact resolve b4e1180 b4e2695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1180 b4e2695
          have b4e3077 : x = (M.op x y) ∨ y = (σ x) := by grind
          clear b4e3068
          have b4e3206 : y = (M.op x y) ∨ y = (σ x) := by
            first
            | (have i₁ := b4e62 x y
               have i₂ := b4e3077
               grind)
            | exact superpose b4e3077 b4e62
            | exact resolve b4e62 b4e3077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e3293 : x = y ∨ y = (σ x) ∨ y = (σ x) := by
            first
            | (have i₁ := b4e3077
               have i₂ := b4e3206
               grind)
            | exact superpose b4e3206 b4e3077
            | exact resolve b4e3077 b4e3206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3077 b4e3206
          have b4e3301 : x = y ∨ y = (σ x) := by grind
          clear b4e3293
          have b4e3308 : y = (σ x) := by
            first
            | (have r₁ := b4e3301
               have r₂ := b4e21
               grind)
            | exact resolve b4e3301 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3301
          have b4e3497 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e3308
               grind)
            | exact superpose b4e3308 b4e23
            | exact resolve b4e23 b4e3308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3308
          have b4e3547 : False := by grind
          exact b4e3547
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b5e192 : y = (M.op (σ y) (σ y)) := by
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
          have b5e202 : y = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e192
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e192
            | exact resolve b5e192 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e192
          have b5e206 : y = (σ y) := by
            first
            | (have i₁ := b5e202
               have i₂ := b5e57 y
               grind)
            | exact superpose b5e57 b5e202
            | exact resolve b5e202 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e202
          have b5e258 : y ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e206
               grind)
            | exact superpose b5e206 b5e24
            | exact resolve b5e24 b5e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e206
          have b5e265 : False := by grind
          exact b5e265
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
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b7e32 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b7e13 x X3 X4
               have i₂ := b7e13 x X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b7e35 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e13 X1 (M.op x X3) X3
               have i₂ := b7e13 X0 x X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
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
          have b7e144 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X1) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b7e13 X2 (M.op x X4) X4
               have i₂ := b7e32 x X4 X0 X1
               grind)
            | (have i₁ := b7e13 X2 (M.op x X4) X4
               have i₂ := b7e32 X0 X1 x X4
               grind)
            | exact superpose b7e32 b7e13
            | exact resolve b7e13 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e145 : ∀ X2 X4 : G, (M.op X2 (M.op X2 X2)) = (M.op (σ y) X4) := by
            intro X2 X4
            first
            | (have i₁ := b7e144 x x X2 X4
               have i₂ := b7e39 x x
               grind)
            | exact superpose b7e39 b7e144
            | exact resolve b7e144 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e144
          have b7e167 : ∀ X4 : G, (σ y) = (M.op (σ y) X4) := by
            intro X4
            first
            | (have i₁ := b7e145 x X4
               have i₂ := b7e37 x
               grind)
            | exact superpose b7e37 b7e145
            | exact resolve b7e145 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e145
          have b7e179 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e30 y
               have i₂ := b7e167 (σ y)
               grind)
            | exact superpose b7e167 b7e30
            | exact resolve b7e30 b7e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e167
          have b7e241 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e179
               grind)
            | exact superpose b7e179 b7e14
            | exact resolve b7e14 b7e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e179
          have b7e242 : y = (M.op y y) := by
            first
            | (have i₁ := b7e241
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e241
            | exact resolve b7e241 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e241
          have b7e360 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op y y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 y X0 X1
               have i₂ := b7e242
               grind)
            | exact superpose b7e242 b7e35
            | exact resolve b7e35 b7e242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e363 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e37 y
               have i₂ := b7e242
               grind)
            | exact superpose b7e242 b7e37
            | exact resolve b7e37 b7e242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e370 : y = (σ y) := by
            first
            | (have i₁ := b7e363
               have i₂ := b7e242
               grind)
            | exact superpose b7e242 b7e363
            | exact resolve b7e363 b7e242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e363
          have b7e373 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e360 X0 X1
               have i₂ := b7e242
               grind)
            | exact superpose b7e242 b7e360
            | exact resolve b7e360 b7e242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e242 b7e360
          have b7e374 : ∀ X1 : G, (σ y) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b7e373 x X1
               have i₂ := b7e37 x
               grind)
            | exact superpose b7e37 b7e373
            | exact resolve b7e373 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37 b7e373
          have b7e375 : ∀ X1 : G, y = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b7e374 X1
               have i₂ := b7e370
               grind)
            | exact superpose b7e370 b7e374
            | exact resolve b7e374 b7e370
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e370 b7e374
          have b7e697 : y ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e375 x
               grind)
            | exact superpose b7e375 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e375 x
               grind)
            | exact resolve b7e22 b7e375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e375
          have b7e714 : False := by grind
          exact b7e714
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b8e64 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0) (σ X0)
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
          have b8e335 : ∀ X0 X2 X3 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X2) = (M.op (σ X3) (σ (M.op X3 X3))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e63 X3 (M.op x X2) X2
               have i₂ := b8e63 X0 x X2
               grind)
            | exact superpose b8e63 b8e63
            | exact resolve b8e63 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e337 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X1) X1) X3) = (M.op (σ X4) (σ (M.op X4 X4))) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b8e63 X4 (M.op x X3) X3
               have i₂ := b8e32 x X3 X0 X1
               grind)
            | (have i₁ := b8e63 X4 (M.op x X3) X3
               have i₂ := b8e32 X0 X1 x X3
               grind)
            | exact superpose b8e32 b8e63
            | exact resolve b8e63 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e344 : ∀ X0 X3 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X3) (σ (M.op X3 X3))) := by
            intro X0 X3
            first
            | (have i₁ := b8e63 X3 x x
               have i₂ := b8e63 X0 x x
               grind)
            | exact superpose b8e63 b8e63
            | exact resolve b8e63 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e369 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e32 X1 X2 (M.op x X4) X4
               have i₂ := b8e63 X0 x X4
               grind)
            | exact superpose b8e63 b8e32
            | exact resolve b8e32 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e400 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e414 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e400
               have r₂ := b8e23
               grind)
            | exact resolve b8e400 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e400
          have b8e485 : ∀ X0 X1 X2 X4 X5 X6 X7 : G, (M.op (M.op (M.op X5 X6) X6) X7) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X4) := by
            intro X0 X1 X2 X4 X5 X6 X7
            first
            | (have i₁ := b8e75 X5 X6 (M.op x X4) X4 X7
               have i₂ := b8e75 X0 X1 x X4 X2
               grind)
            | (have i₁ := b8e75 X0 X1 (M.op (M.op X0 X1) X1) X5 X5
               have i₂ := b8e75 X0 X1 X2 x X5
               grind)
            | exact superpose b8e75 b8e75
            | exact resolve b8e75 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e486 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X2) = (M.op (M.op (M.op X3 X4) X4) X5) := by
            intro X0 X2 X3 X4 X5
            first
            | (have i₁ := b8e75 X3 X4 (M.op x X2) X2 X5
               have i₂ := b8e63 X0 x X2
               grind)
            | exact superpose b8e63 b8e75
            | exact resolve b8e75 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e561 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) X1) X2) X4) = (M.op (σ X5) (σ (M.op X5 X5))) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b8e63 X5 (M.op x X4) X4
               have i₂ := b8e75 X0 X1 x X4 X2
               grind)
            | (have i₁ := b8e63 X0 (M.op (M.op X0 X1) X1) X5
               have i₂ := b8e75 X0 X1 X2 x X5
               grind)
            | exact superpose b8e75 b8e63
            | exact resolve b8e63 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e6229 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e414
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e414
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e414
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e414
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e414 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e414
          have b8e6230 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e6229
          have b8e6231 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e6230
               have r₂ := b8e21
               grind)
            | exact resolve b8e6230 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6230
          have b8e6235 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e6231
               grind)
            | exact superpose b8e6231 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e6231
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e6231
               grind)
            | exact resolve b8e17 b8e6231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e6255 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e6235
          have b8e6257 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e6255
               have r₂ := b8e23
               grind)
            | exact resolve b8e6255 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6255
          have b8e6260 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e6257
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e6257
            | exact resolve b8e6257 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6257
          have b8e7279 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e6260
               grind)
            | exact superpose b8e6260 b8e14
            | exact resolve b8e14 b8e6260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6260
          have b8e7334 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e7279
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e7279
            | exact resolve b8e7279 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7279
          have b8e7826 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e18 y x
               have i₂ := b8e7334
               grind)
            | exact superpose b8e7334 b8e18
            | (have j0 := b8e18 y x
               grind)
            | exact resolve b8e18 b8e7334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7334
          have b8e7827 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e7826
          have b8e7829 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e7827
               have r₂ := b8e21
               grind)
            | exact resolve b8e7827 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7827
          have b8e7853 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ y = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 x y
               have i₂ := b8e7829
               grind)
            | exact superpose b8e7829 b8e32
            | exact resolve b8e32 b8e7829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e8743 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            intro X1
            first
            | (have i₁ := b8e7853 (M.op x X1) X1
               have i₂ := b8e7853 x X1
               grind)
            | exact superpose b8e7853 b8e7853
            | exact resolve b8e7853 b8e7853
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e8917 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ y = (M.op x y) := by
            intro X1
            first
            | (have j0 := b8e8743 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8743
          have b8e8980 : ∀ X0 : G, x = (M.op x X0) ∨ x = y ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e8917 x
               have i₂ := b8e7829
               grind)
            | exact superpose b8e7829 b8e8917
            | exact resolve b8e8917 b8e7829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7829 b8e8917
          have b8e9154 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e8980 X0
               grind)
            | (have r₁ := b8e8980 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e8980 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8980
          have b8e9843 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e7853 x X0
               have i₂ := b8e9154 X0
               grind)
            | exact superpose b8e9154 b8e7853
            | exact resolve b8e7853 b8e9154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7853
          have b8e9846 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e35 X0 x
               have i₂ := b8e9154 (M.op x x)
               grind)
            | exact superpose b8e9154 b8e35
            | exact resolve b8e35 b8e9154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e9882 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e9843 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9843
          have b8e10128 : ∀ X1 : G, x = (M.op (σ (M.op X1 X1)) (σ X1)) ∨ y = (M.op x y) := by
            intro X1
            first
            | (have i₁ := b8e64 X1 x
               have i₂ := b8e9846 x
               grind)
            | exact superpose b8e9846 b8e64
            | exact resolve b8e64 b8e9846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e10218 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) X1) ∨ y = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b8e75 x x X0 X1 (M.op (M.op (M.op x x) x) (M.op (M.op x x) x))
               have i₂ := b8e9846 (M.op (M.op x x) x)
               grind)
            | exact superpose b8e9846 b8e75
            | exact resolve b8e75 b8e9846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75 b8e9846
          have b8e10348 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x X0) ∨ y = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b8e9882 X0
               have i₂ := b8e9882 X0
               grind)
            | (have i₁ := b8e9882 X0
               have i₂ := b8e9882 y
               grind)
            | exact superpose b8e9882 b8e9882
            | exact resolve b8e9882 b8e9882
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e10486 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (M.op x y) := by
            intro X0
            grind
          clear b8e9882
          have b8e10496 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
            intro X0 X1
            first
            | (have j0 := b8e10348 X0 X1
               grind)
            | (have r₁ := b8e10348 X0 X1
               have r₂ := b8e10486 X0
               grind)
            | (have r₁ := b8e10348 X0 X1
               have r₂ := b8e10486 y
               grind)
            | exact resolve b8e10348 b8e10486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10348 b8e10486
          have b8e11899 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b8e10218 x X1
               have i₂ := b8e10496 X1 X0
               grind)
            | (have i₁ := b8e10218 x X1
               have i₂ := b8e10496 X0 X1
               grind)
            | exact superpose b8e10496 b8e10218
            | exact resolve b8e10218 b8e10496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10218
          have b8e11946 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
            intro X0 X1
            first
            | (have j0 := b8e11899 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11899
          have b8e17967 : x = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e10128 x
               have i₂ := b8e9154 x
               grind)
            | exact superpose b8e9154 b8e10128
            | exact resolve b8e10128 b8e9154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9154 b8e10128
          have b8e18052 : x = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e17967
          have b8e18066 : x = (σ (M.op x x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e18052
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e18052
            | exact resolve b8e18052 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18052
          have b8e18130 : ∀ X0 : G, x = (σ (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e18066
               have i₂ := b8e10496 x X0
               grind)
            | (have i₁ := b8e18066
               have i₂ := b8e10496 X0 x
               grind)
            | exact superpose b8e10496 b8e18066
            | exact resolve b8e18066 b8e10496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10496
          have b8e18147 : (M.op x x) = (τ x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e18066
               grind)
            | exact superpose b8e18066 b8e14
            | exact resolve b8e14 b8e18066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18066
          have b8e18201 : ∀ X0 : G, x = (σ (M.op x X0)) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e18130 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18130
          have b8e18707 : ∀ X0 : G, x = (M.op (τ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e11946 x X0
               have i₂ := b8e18147
               grind)
            | exact superpose b8e18147 b8e11946
            | exact resolve b8e11946 b8e18147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18147
          have b8e18827 : ∀ X0 : G, x = (M.op (τ x) X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e18707 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18707
          have b8e23708 : (σ x) = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e42 x
               have i₂ := b8e18827 (τ x)
               grind)
            | exact superpose b8e18827 b8e42
            | exact resolve b8e42 b8e18827
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e18827
          have b8e28794 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e11946 x X0
               have i₂ := b8e23708
               grind)
            | exact superpose b8e23708 b8e11946
            | exact resolve b8e11946 b8e23708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11946 b8e23708
          have b8e28933 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e28794 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28794
          have b8e36957 : x ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e28933 (σ y)
               grind)
            | exact superpose b8e28933 b8e20
            | exact resolve b8e20 b8e28933
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28933
          have b8e37207 : y = (M.op x y) := by
            first
            | (have r₁ := b8e36957
               have r₂ := b8e18201 y
               grind)
            | exact resolve b8e36957 b8e18201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18201 b8e36957
          have b8e38249 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x y
               have i₂ := b8e37207
               grind)
            | exact superpose b8e37207 b8e13
            | exact resolve b8e13 b8e37207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e38252 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 x y
               have i₂ := b8e37207
               grind)
            | exact superpose b8e37207 b8e32
            | exact resolve b8e32 b8e37207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e39809 : ∀ X2 : G, (M.op (σ X2) (σ (M.op X2 X2))) = (M.op y y) := by
            intro X2
            first
            | (have i₁ := b8e337 x x (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) X2
               have i₂ := b8e38249 (M.op (M.op x x) x)
               grind)
            | exact superpose b8e38249 b8e337
            | exact resolve b8e337 b8e38249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e337
          have b8e39812 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) = (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b8e486 X0 X1 x x (M.op (M.op (M.op x x) x) (M.op (M.op x x) x))
               have i₂ := b8e38249 (M.op (M.op x x) x)
               grind)
            | exact superpose b8e38249 b8e486
            | exact resolve b8e486 b8e38249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e486
          have b8e39829 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op y y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e485 x x x (M.op (M.op (M.op (M.op x x) x) x) (M.op (M.op (M.op x x) x) x)) X0 X1 X2
               have i₂ := b8e38249 (M.op (M.op (M.op x x) x) x)
               grind)
            | exact superpose b8e38249 b8e485
            | exact resolve b8e485 b8e38249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e485 b8e38249
          have b8e39853 : ∀ X2 : G, (M.op y y) = (M.op (M.op y y) X2) := by
            intro X2
            first
            | (have i₁ := b8e39829 x x X2
               have i₂ := b8e38252 x x
               grind)
            | exact superpose b8e38252 b8e39829
            | exact resolve b8e39829 b8e38252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39829
          have b8e40825 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (σ X1) (σ (M.op X1 X1))) X2) = (M.op (σ (M.op (M.op (M.op X3 X4) X4) X5)) (σ (M.op (σ X0) (σ (M.op X0 X0))))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e335 X1 X2 (M.op (M.op (M.op X3 X4) X4) X5)
               have i₂ := b8e561 X3 X4 X5 (M.op (M.op (M.op X3 X4) X4) X5) X0
               grind)
            | exact superpose b8e561 b8e335
            | exact resolve b8e335 b8e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e335 b8e561
          have b8e41089 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op (σ X1) (σ (M.op X1 X1))) X2) = (M.op (σ (M.op (M.op (M.op X3 X4) X4) X5)) (σ (M.op y y))) := by
            intro X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e40825 x X1 X2 X3 X4 X5
               have i₂ := b8e39809 x
               grind)
            | exact superpose b8e39809 b8e40825
            | exact resolve b8e40825 b8e39809
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40825
          have b8e41194 : ∀ X1 X2 X5 : G, (M.op (M.op (σ X1) (σ (M.op X1 X1))) X2) = (M.op (σ (M.op (M.op y y) X5)) (σ (M.op y y))) := by
            intro X1 X2 X5
            first
            | (have i₁ := b8e41089 X1 X2 x x X5
               have i₂ := b8e38252 x x
               grind)
            | exact superpose b8e38252 b8e41089
            | exact resolve b8e41089 b8e38252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41089
          have b8e41283 : ∀ X1 X2 : G, (M.op (M.op (σ X1) (σ (M.op X1 X1))) X2) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            intro X1 X2
            first
            | (have i₁ := b8e41194 X1 X2 x
               have i₂ := b8e39853 x
               grind)
            | exact superpose b8e39853 b8e41194
            | exact resolve b8e41194 b8e39853
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41194
          have b8e41367 : ∀ X1 X2 : G, (M.op (M.op (σ X1) (σ (M.op X1 X1))) X2) = (σ (M.op (M.op y y) (M.op y y))) := by
            intro X1 X2
            first
            | (have i₁ := b8e41283 X1 X2
               have i₂ := b8e30 (M.op y y)
               grind)
            | exact superpose b8e30 b8e41283
            | exact resolve b8e41283 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e41283
          have b8e41438 : ∀ X1 X2 : G, (M.op (M.op (σ X1) (σ (M.op X1 X1))) X2) = (σ (M.op y y)) := by
            intro X1 X2
            first
            | (have i₁ := b8e41367 X1 X2
               have i₂ := b8e39853 (M.op y y)
               grind)
            | exact superpose b8e39853 b8e41367
            | exact resolve b8e41367 b8e39853
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39853 b8e41367
          have b8e41494 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e41438 x x
               have i₂ := b8e39812 x x
               grind)
            | exact superpose b8e39812 b8e41438
            | exact resolve b8e41438 b8e39812
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39812 b8e41438
          have b8e41625 : (M.op y y) = (τ (M.op y y)) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e41494
               grind)
            | exact superpose b8e41494 b8e14
            | exact resolve b8e14 b8e41494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e45875 : (M.op (σ x) (σ y)) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e38252 (σ x) (σ y)
               have i₂ := b8e6231
               grind)
            | exact superpose b8e6231 b8e38252
            | exact resolve b8e38252 b8e6231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e46323 : x = y ∨ (M.op (σ x) (σ y)) = (M.op y y) := by
            first
            | (have i₁ := b8e45875
               have i₂ := b8e37207
               grind)
            | exact superpose b8e37207 b8e45875
            | exact resolve b8e45875 b8e37207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45875
          have b8e46474 : (M.op (σ x) (σ y)) = (M.op y y) := by
            first
            | (have r₁ := b8e46323
               have r₂ := b8e21
               grind)
            | exact resolve b8e46323 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46323
          have b8e50490 : (σ x) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e6231
               have i₂ := b8e46474
               grind)
            | exact superpose b8e46474 b8e6231
            | exact resolve b8e6231 b8e46474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6231 b8e46474
          have b8e50580 : x = y ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b8e50490
               have i₂ := b8e37207
               grind)
            | exact superpose b8e37207 b8e50490
            | exact resolve b8e50490 b8e37207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50490
          have b8e50588 : (σ x) = (M.op y y) := by
            first
            | (have r₁ := b8e50580
               have r₂ := b8e21
               grind)
            | exact resolve b8e50580 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50580
          have b8e55463 : (σ x) = (τ (σ x)) := by
            first
            | (have i₁ := b8e41625
               have i₂ := b8e50588
               grind)
            | exact superpose b8e50588 b8e41625
            | exact resolve b8e41625 b8e50588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41625
          have b8e55464 : (σ x) = (σ (σ x)) := by
            first
            | (have i₁ := b8e41494
               have i₂ := b8e50588
               grind)
            | exact superpose b8e50588 b8e41494
            | exact resolve b8e41494 b8e50588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41494
          have b8e55529 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ y) (σ (σ x))) := by
            intro X0
            first
            | (have i₁ := b8e344 X0 y
               have i₂ := b8e50588
               grind)
            | exact superpose b8e50588 b8e344
            | exact resolve b8e344 b8e50588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e344
          have b8e55531 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ y) (σ (σ x))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e369 y X0 X1 X2
               have i₂ := b8e50588
               grind)
            | exact superpose b8e50588 b8e369
            | exact resolve b8e369 b8e50588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e369
          have b8e55684 : ∀ X2 : G, (M.op y y) = (M.op (M.op (σ y) (σ (σ x))) X2) := by
            intro X2
            first
            | (have i₁ := b8e55531 x x X2
               have i₂ := b8e38252 x x
               grind)
            | exact superpose b8e38252 b8e55531
            | exact resolve b8e55531 b8e38252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38252 b8e55531
          have b8e55686 : (M.op y y) = (M.op (σ y) (σ (σ x))) := by
            first
            | (have i₁ := b8e55529 x
               have i₂ := b8e39809 x
               grind)
            | exact superpose b8e39809 b8e55529
            | exact resolve b8e55529 b8e39809
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39809 b8e55529
          have b8e55721 : x = (σ x) := by
            first
            | (have i₁ := b8e55463
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e55463
            | exact resolve b8e55463 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55463
          have b8e55783 : ∀ X2 : G, (M.op y y) = (M.op (M.op (σ y) (σ x)) X2) := by
            intro X2
            first
            | (have i₁ := b8e55684 X2
               have i₂ := b8e55464
               grind)
            | exact superpose b8e55464 b8e55684
            | exact resolve b8e55684 b8e55464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55684
          have b8e55785 : (M.op (σ y) (σ x)) = (M.op y y) := by
            first
            | (have i₁ := b8e55686
               have i₂ := b8e55464
               grind)
            | exact superpose b8e55464 b8e55686
            | exact resolve b8e55686 b8e55464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55464 b8e55686
          have b8e55866 : ∀ X2 : G, (M.op y y) = (M.op (M.op (σ y) x) X2) := by
            intro X2
            first
            | (have i₁ := b8e55783 X2
               have i₂ := b8e55721
               grind)
            | exact superpose b8e55721 b8e55783
            | exact resolve b8e55783 b8e55721
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55783
          have b8e55868 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e55785
               have i₂ := b8e50588
               grind)
            | exact superpose b8e50588 b8e55785
            | exact resolve b8e55785 b8e50588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55785
          have b8e55925 : ∀ X2 : G, (σ x) = (M.op (M.op (σ y) x) X2) := by
            intro X2
            first
            | (have i₁ := b8e55866 X2
               have i₂ := b8e50588
               grind)
            | exact superpose b8e50588 b8e55866
            | exact resolve b8e55866 b8e50588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50588 b8e55866
          have b8e55927 : x = (M.op (σ y) x) := by
            first
            | (have i₁ := b8e55868
               have i₂ := b8e55721
               grind)
            | exact superpose b8e55721 b8e55868
            | exact resolve b8e55868 b8e55721
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55868
          have b8e55959 : ∀ X2 : G, x = (M.op (M.op (σ y) x) X2) := by
            intro X2
            first
            | (have i₁ := b8e55925 X2
               have i₂ := b8e55721
               grind)
            | exact superpose b8e55721 b8e55925
            | exact resolve b8e55925 b8e55721
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55721 b8e55925
          have b8e55970 : ∀ X2 : G, x = (M.op x X2) := by
            intro X2
            first
            | (have i₁ := b8e55959 X2
               have i₂ := b8e55927
               grind)
            | exact superpose b8e55927 b8e55959
            | exact resolve b8e55959 b8e55927
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55927 b8e55959
          have b8e63839 : x = y := by
            first
            | (have i₁ := b8e37207
               have i₂ := b8e55970 y
               grind)
            | exact superpose b8e55970 b8e37207
            | exact resolve b8e37207 b8e55970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37207 b8e55970
          have b8e64243 : False := by grind
          exact b8e64243
