import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_y_x_pxy_Equation3744 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
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
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : x ≠ x ∨ y = (k x y) := by
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
        clear b1e25
        have b1e53 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        have b1e57 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e53
             have r₂ := b1e21
             grind)
          | exact resolve b1e53 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e59 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e57
          | exact resolve b1e57 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e60 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e59
          | exact resolve b1e59 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e59
        have b1e61 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e21
          | exact resolve b1e21 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e61
          | exact resolve b1e61 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e69 : False := by grind
        exact b1e69
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : x ≠ x ∨ y = (k x y) := by
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
        have b2e26 : y = (k x y) := by grind
        clear b2e25
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
        have b2e33 : ∀ X0 X1 : G, (M.op x X0) = (M.op x (M.op X1 X0)) := by
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
        have b2e34 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
          intro X0 X1 X2 X3 X5
          first
          | (have i₁ := b2e12 (M.op X0 X2) X3 (M.op x X1) X5
             have i₂ := b2e12 X0 X1 X2 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) x) := by
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
        have b2e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b2e12 X0 X1 x X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X3 X1) = (k (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e15 (M.op X0 X2) (M.op X3 X1)
             have i₂ := b2e12 X0 X1 X2 X3
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op X0 X2) (M.op X3 X1)
             grind)
          | (have r₁ := b2e15 (M.op X0 X1) (M.op X3 X1)
             have r₂ := b2e12 X0 X1 X1 X3
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b2e36 x X1 X2 X3 x
             have i₂ := b2e12 X2 X1 x x
             grind)
          | exact superpose b2e12 b2e36
          | exact resolve b2e36 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e39 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b2e34 X0 x X2 X3 x
             have i₂ := b2e12 X0 X3 x x
             grind)
          | exact superpose b2e12 b2e34
          | exact resolve b2e34 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e40 : x = (M.op x x) := by
          first
          | (have i₁ := b2e33 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e33
          | exact resolve b2e33 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b2e15 x x
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e15
          | (have j0 := b2e15 x x
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e40
             grind)
          | exact resolve b2e15 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : x = (k x x) := by grind
        clear b2e55
        have b2e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e66 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X1 X3) X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X2 X3 X2
             have i₂ := b2e17 X2 X0
             grind)
          | (have i₁ := b2e12 X0 X1 X2 X3
             have i₂ := b2e17 X0 (M.op X3 X1)
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X2 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X2 X1 X3
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e12 X0 X1 X2 X3
             have i₂ := b2e17 X0 (M.op X0 X2)
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X1 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
        have b2e74 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e67 X0 X1 X2 x
             have i₂ := b2e38 X2 X0 x
             grind)
          | exact superpose b2e38 b2e67
          | (have j0 := b2e67 X0 X1 X2 x
             grind)
          | exact resolve b2e67 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e75 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e66 X0 X1 X2 x
             have i₂ := b2e39 X1 x X0
             grind)
          | exact superpose b2e39 b2e66
          | (have j0 := b2e66 X0 X1 X2 x
             grind)
          | exact resolve b2e66 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e90 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op (M.op X1 X2) (M.op X0 y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 x X2 (M.op X0 x)
             have i₂ := b2e35 X0 x
             grind)
          | exact superpose b2e35 b2e12
          | exact resolve b2e12 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e94 : ∀ X1 : G, (M.op X1 y) = (M.op X1 x) := by
          intro X1
          first
          | (have i₁ := b2e90 x X1 x
             have i₂ := b2e12 X1 y x x
             grind)
          | exact superpose b2e12 b2e90
          | exact resolve b2e90 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e185 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e188 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e32
          | exact resolve b2e32 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e245 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X2 X1) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e37 X2 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e285 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (M.op (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e74 (σ X1) (σ X0) X2
             grind)
          | exact superpose b2e74 b2e18
          | (have j1 := b2e74 (σ X1) (σ X0) X2
             grind)
          | exact resolve b2e18 b2e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e418 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 X2
             have i₂ := b2e75 X2 X0 X1
             grind)
          | (have i₁ := b2e15 X1 X2
             have i₂ := b2e75 X0 X1 X2
             grind)
          | exact superpose b2e75 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e75 X2 X1 X1
             grind)
          | (have r₁ := b2e15 X2 X0
             have r₂ := b2e75 X0 X1 X2
             grind)
          | exact resolve b2e15 b2e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e429 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) ∨ (M.op X1 y) = (k X1 y) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e94 X0
             have i₂ := b2e75 y X0 X1
             grind)
          | (have i₁ := b2e94 X1
             have i₂ := b2e75 X0 X1 y
             grind)
          | exact superpose b2e75 b2e94
          | (have j1 := b2e75 y X1 X1
             grind)
          | exact resolve b2e94 b2e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e435 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X2 ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X0 X2
             have i₂ := b2e75 X1 X0 X0
             grind)
          | (have i₁ := b2e17 X0 X1
             have i₂ := b2e75 X0 X0 X2
             grind)
          | exact superpose b2e75 b2e17
          | (have j0 := b2e17 X0 X2
             have j1 := b2e75 X2 X1 X0
             grind)
          | exact resolve b2e17 b2e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e436 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e454 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e75 X0 (σ x) (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e75 (σ y) (σ x) x
             grind)
          | exact superpose b2e75 b2e21
          | (have j1 := b2e75 X0 x (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e75 (σ y) x (σ x)
             grind)
          | exact resolve b2e21 b2e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e455 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e75 X0 (σ x) (σ x)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e75 (σ x) (σ x) x
             grind)
          | exact superpose b2e75 b2e22
          | (have j1 := b2e75 X0 x (σ x)
             grind)
          | exact resolve b2e22 b2e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e456 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e75 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e466 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e436 X0 X1
             have i₂ := b2e38 X1 X0 X0
             grind)
          | exact superpose b2e38 b2e436
          | (have j0 := b2e436 X0 X1
             grind)
          | exact resolve b2e436 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e436
        have b2e467 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e466 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e466
        have b2e471 : ∀ X0 X1 : G, (M.op X1 x) = (k X1 y) ∨ (M.op X0 X1) = (M.op X0 x) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e429 X0 X1
             have i₂ := b2e94 X1
             grind)
          | exact superpose b2e94 b2e429
          | (have j0 := b2e429 X0 X1
             grind)
          | exact resolve b2e429 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e429
        have b2e491 : ∀ X0 X1 : G, (M.op X1 x) = (k X1 y) ∨ (M.op X0 X1) = (M.op X0 x) ∨ (M.op X1 x) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e471 X0 X1
             have i₂ := b2e94 X1
             grind)
          | exact superpose b2e94 b2e471
          | (have j0 := b2e471 X0 X1
             grind)
          | exact resolve b2e471 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e471
        have b2e506 : ∀ X0 : G, (M.op X0 x) = (k x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e245 X0 x x
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e245
          | exact resolve b2e245 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e563 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e71 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e564 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e563
             have r₂ := b2e21
             grind)
          | exact resolve b2e563 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e563
        have b2e565 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e564
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e564
          | exact resolve b2e564 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e564
        have b2e566 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e565
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e565
          | exact resolve b2e565 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e565
        have b2e571 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e566
             grind)
          | exact superpose b2e566 b2e21
          | exact resolve b2e21 b2e566
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e578 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e39 (σ x) (σ y) X0
             have i₂ := b2e566
             grind)
          | exact superpose b2e566 b2e39
          | exact resolve b2e39 b2e566
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e583 : ∀ X0 : G, (σ y) = (k (M.op X0 (σ y)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e245 (σ x) (σ y) x
             have i₂ := b2e566
             grind)
          | exact superpose b2e566 b2e245
          | exact resolve b2e245 b2e566
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e671 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e39 (σ X0) (σ X1) X2
             have i₂ := b2e62 X0 X1
             grind)
          | exact superpose b2e62 b2e39
          | (have j1 := b2e62 X0 X1
             grind)
          | exact resolve b2e39 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e706 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e62 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e708 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e706 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e706
        have b2e952 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b2e583 (σ x)
             have i₂ := b2e566
             grind)
          | exact superpose b2e566 b2e583
          | exact resolve b2e583 b2e566
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e583
        have b2e970 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b2e952
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e952
          | exact resolve b2e952 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e952
        have b2e1024 : (τ (σ y)) = (k y y) := by
          first
          | (have i₁ := b2e13 (k y y)
             have i₂ := b2e970
             grind)
          | exact superpose b2e970 b2e13
          | exact resolve b2e13 b2e970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1027 : ∀ X0 : G, (k (τ X0) (k y y)) = (τ (k X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b2e32 X0 (k y y)
             have i₂ := b2e970
             grind)
          | exact superpose b2e970 b2e32
          | exact resolve b2e32 b2e970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e970
        have b2e1036 : ∀ X0 : G, (k (τ X0) (k y y)) = (k (τ X0) y) := by
          intro X0
          first
          | (have i₁ := b2e1027 X0
             have i₂ := b2e32 X0 y
             grind)
          | exact superpose b2e32 b2e1027
          | exact resolve b2e1027 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1027
        have b2e1039 : y = (k y y) := by
          first
          | (have i₁ := b2e1024
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e1024
          | exact resolve b2e1024 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1024
        have b2e1086 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e17 y y
             have i₂ := b2e1039
             grind)
          | exact superpose b2e1039 b2e17
          | (have j0 := b2e17 y y
             grind)
          | exact resolve b2e17 b2e1039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1087 : y = (M.op y y) := by grind
        clear b2e1086
        have b2e1094 : y = (M.op y x) := by
          first
          | (have i₁ := b2e1087
             have i₂ := b2e94 y
             grind)
          | exact superpose b2e94 b2e1087
          | exact resolve b2e1087 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1087
        have b2e1164 : ∀ X0 : G, (M.op X0 x) = (k y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e245 X0 x y
             have i₂ := b2e1094
             grind)
          | exact superpose b2e1094 b2e245
          | exact resolve b2e245 b2e1094
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1523 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e708 x
             have i₂ := b2e57
             grind)
          | exact superpose b2e57 b2e708
          | (have j0 := b2e708 x
             grind)
          | exact resolve b2e708 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1526 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e708 (τ X0)
             have i₂ := b2e28 X0 (τ X0)
             grind)
          | exact superpose b2e28 b2e708
          | (have j0 := b2e708 (τ X0)
             grind)
          | exact resolve b2e708 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e708
        have b2e1531 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e1523
        have b2e1535 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e1526 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1526
          | (have j0 := b2e1526 X0
             grind)
          | exact resolve b2e1526 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1526
        have b2e1539 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1535 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1535
          | (have j0 := b2e1535 X0
             grind)
          | exact resolve b2e1535 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1535
        have b2e1570 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b2e245 X0 (σ x) (σ x)
             have i₂ := b2e1531
             grind)
          | exact superpose b2e1531 b2e245
          | exact resolve b2e245 b2e1531
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e245
        have b2e1676 : ∀ X0 : G, y ≠ (M.op y x) ∨ (M.op y X0) = (k y X0) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e456 y X0
             have i₂ := b2e94 y
             grind)
          | exact superpose b2e94 b2e456
          | (have j0 := b2e456 y X0
             grind)
          | exact resolve b2e456 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1683 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e456 x X0
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e456
          | (have j0 := b2e456 x X0
             grind)
          | (have r₁ := b2e456 x x
             have r₂ := b2e40
             grind)
          | exact resolve b2e456 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e456
        have b2e1684 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b2e1683 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1683
        have b2e1692 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b2e1676 X0
             grind)
          | (have r₁ := b2e1676 X0
             have r₂ := b2e1094
             grind)
          | exact resolve b2e1676 b2e1094
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1676
        have b2e1951 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e1539 (τ X0)
             have i₂ := b2e188 X0 X0
             grind)
          | exact superpose b2e188 b2e1539
          | (have j0 := b2e1539 (τ X0)
             grind)
          | exact resolve b2e1539 b2e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e188 b2e1539
        have b2e2201 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e467 X2 (M.op x X1)
             have i₂ := b2e38 X1 X2 x
             grind)
          | exact superpose b2e38 b2e467
          | (have j0 := b2e467 X0 X1
             grind)
          | exact resolve b2e467 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e467
        have b2e3912 : ∀ X0 : G, (k (τ x) X0) = (τ (M.op x (σ X0))) ∨ x = (M.op x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e32 x X0
             have i₂ := b2e1684 (σ X0)
             grind)
          | exact superpose b2e1684 b2e32
          | (have j1 := b2e1684 (σ X0)
             grind)
          | exact resolve b2e32 b2e1684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1684
        have b2e3980 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op y (σ X0))) ∨ y = (M.op y (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e32 y X0
             have i₂ := b2e1692 (σ X0)
             grind)
          | exact superpose b2e1692 b2e32
          | (have j1 := b2e1692 (σ X0)
             grind)
          | exact resolve b2e32 b2e1692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1692
        have b2e4794 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) (M.op X1 X0)) = (k (σ y) (M.op X1 X0)) ∨ (σ y) = (M.op (σ y) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e454 (M.op X1 X0)
             have i₂ := b2e38 X0 (σ x) X1
             grind)
          | exact superpose b2e38 b2e454
          | (have j0 := b2e454 (M.op X1 X0)
             grind)
          | exact resolve b2e454 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e454
        have b2e4798 : ∀ X0 X1 : G, (M.op (σ y) X0) = (k (σ y) (M.op X1 X0)) ∨ (σ x) ≠ (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e4794 X0 X1
             have i₂ := b2e38 X0 (σ y) X1
             grind)
          | exact superpose b2e38 b2e4794
          | (have j0 := b2e4794 X0 X1
             grind)
          | exact resolve b2e4794 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4794
        have b2e4807 : ∀ X0 X1 : G, (M.op (σ x) X0) = (k (σ y) (M.op X1 X0)) ∨ (σ x) ≠ (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e4798 X0 X1
             have i₂ := b2e578 X0
             grind)
          | exact superpose b2e578 b2e4798
          | (have j0 := b2e4798 X0 X1
             grind)
          | exact resolve b2e4798 b2e578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4798
        have b2e4816 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op (σ x) X0) = (k (σ y) (M.op X1 X0)) ∨ (σ x) ≠ (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e4807 X0 X1
             have i₂ := b2e38 X0 (σ y) X1
             grind)
          | exact superpose b2e38 b2e4807
          | (have j0 := b2e4807 X0 X1
             grind)
          | exact resolve b2e4807 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e4807
        have b2e4820 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ y) (M.op X1 X0)) ∨ (σ y) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e4816 X0 X1
             have i₂ := b2e578 X0
             grind)
          | exact superpose b2e578 b2e4816
          | (have j0 := b2e4816 X0 X1
             grind)
          | exact resolve b2e4816 b2e578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4816
        have b2e4883 : (σ y) ≠ (M.op (σ x) x) ∨ (M.op (σ x) x) = (k (σ x) y) ∨ (σ x) = (M.op (σ x) x) := by
          first
          | (have i₁ := b2e455 y
             have i₂ := b2e94 (σ x)
             grind)
          | exact superpose b2e94 b2e455
          | (have j0 := b2e455 x
             grind)
          | exact resolve b2e455 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e455
        have b2e10401 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X1) X2) = (M.op (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e285 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e285
        have b2e12812 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
          first
          | (have i₁ := b2e1951 x
             have i₂ := b2e57
             grind)
          | exact superpose b2e57 b2e1951
          | (have j0 := b2e1951 x
             grind)
          | exact resolve b2e1951 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e12814 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
          first
          | (have i₁ := b2e1951 y
             have i₂ := b2e1039
             grind)
          | exact superpose b2e1039 b2e1951
          | (have j0 := b2e1951 y
             grind)
          | exact resolve b2e1951 b2e1039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1951
        have b2e12823 : (τ y) = (M.op (τ y) (τ y)) := by grind
        clear b2e12814
        have b2e12824 : (τ x) = (M.op (τ x) (τ x)) := by grind
        clear b2e12812
        have b2e12974 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (M.op X0 X2) = (M.op (σ (k (τ X0) X1)) X2) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e671 (τ X0) X1 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e671
          | exact resolve b2e671 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e671
        have b2e13340 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 (σ X1)) X2) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12974 X0 X1 X2
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e12974
          | (have j0 := b2e12974 X0 X1 X2
             grind)
          | exact resolve b2e12974 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12974
        have b2e13533 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (k (τ x) X0) = X0 ∨ (k (τ x) X0) = (M.op (τ x) X0) ∨ (τ x) = (M.op (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e418 (τ x) (τ x) X0
             have i₂ := b2e12824
             grind)
          | exact superpose b2e12824 b2e418
          | (have j0 := b2e418 (τ x) (τ x) X0
             grind)
          | (have r₁ := b2e418 (τ x) (τ x) x
             have r₂ := b2e12824
             grind)
          | exact resolve b2e418 b2e12824
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e13543 : ∀ X0 : G, (k (τ x) X0) = X0 ∨ (k (τ x) X0) = (M.op (τ x) X0) ∨ (τ x) = (M.op (τ x) X0) := by
          intro X0
          first
          | (have j0 := b2e13533 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13533
        have b2e13552 : ∀ X0 : G, (k (τ x) X0) = (M.op (τ x) X0) ∨ (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e13543 X0
             have j1 := b2e15 (τ x) X0
             grind)
          | (have r₁ := b2e13543 x
             have r₂ := b2e15 (τ x) x
             grind)
          | exact resolve b2e13543 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13543
        have b2e13789 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (k (τ y) X0) = X0 ∨ (k (τ y) X0) = (M.op (τ y) X0) ∨ (τ y) = (M.op (τ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e418 (τ y) (τ y) X0
             have i₂ := b2e12823
             grind)
          | exact superpose b2e12823 b2e418
          | (have j0 := b2e418 (τ y) (τ y) X0
             grind)
          | (have r₁ := b2e418 (τ y) (τ y) x
             have r₂ := b2e12823
             grind)
          | exact resolve b2e418 b2e12823
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e418 b2e12823
        have b2e13799 : ∀ X0 : G, (k (τ y) X0) = X0 ∨ (k (τ y) X0) = (M.op (τ y) X0) ∨ (τ y) = (M.op (τ y) X0) := by
          intro X0
          first
          | (have j0 := b2e13789 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13789
        have b2e13808 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e13799 X0
             have j1 := b2e15 (τ y) X0
             grind)
          | (have r₁ := b2e13799 x
             have r₂ := b2e15 (τ y) x
             grind)
          | exact resolve b2e13799 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13799
        have b2e17067 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e435 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e435
        have b2e17069 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e17067 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17067
        have b2e17070 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e17069 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17069
        have b2e32458 : (k (τ x) y) = (M.op (τ x) (k y y)) ∨ (k y y) = (k (τ x) y) := by
          first
          | (have i₁ := b2e13552 (k y y)
             have i₂ := b2e1036 x
             grind)
          | exact superpose b2e1036 b2e13552
          | exact resolve b2e13552 b2e1036
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32519 : ∀ X0 : G, (M.op (τ x) X0) ≠ X0 ∨ (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e13552 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32544 : (M.op (τ x) y) = (k (τ x) y) ∨ (k y y) = (k (τ x) y) := by
          first
          | (have i₁ := b2e32458
             have i₂ := b2e1039
             grind)
          | exact superpose b2e1039 b2e32458
          | exact resolve b2e32458 b2e1039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32458
        have b2e32559 : (M.op (τ x) x) = (k (τ x) y) ∨ (k y y) = (k (τ x) y) := by
          first
          | (have i₁ := b2e32544
             have i₂ := b2e94 (τ x)
             grind)
          | exact superpose b2e94 b2e32544
          | exact resolve b2e32544 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32544
        have b2e32570 : (M.op (τ x) x) = (k (τ x) y) ∨ y = (k (τ x) y) := by
          first
          | (have i₁ := b2e32559
             have i₂ := b2e1039
             grind)
          | exact superpose b2e1039 b2e32559
          | exact resolve b2e32559 b2e1039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32559
        have b2e33172 : y ≠ (M.op (τ x) x) ∨ y = (k (τ x) y) := by
          first
          | (have i₁ := b2e32519 y
             have i₂ := b2e94 (τ x)
             grind)
          | exact superpose b2e94 b2e32519
          | (have j0 := b2e32519 y
             grind)
          | exact resolve b2e32519 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38220 : (k (τ y) y) = (M.op (τ y) (k y y)) ∨ (k y y) = (k (τ y) y) := by
          first
          | (have i₁ := b2e13808 (k y y)
             have i₂ := b2e1036 y
             grind)
          | exact superpose b2e1036 b2e13808
          | exact resolve b2e13808 b2e1036
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1036
        have b2e38286 : ∀ X0 : G, (M.op (τ y) X0) ≠ X0 ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e13808 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38313 : (M.op (τ y) y) = (k (τ y) y) ∨ (k y y) = (k (τ y) y) := by
          first
          | (have i₁ := b2e38220
             have i₂ := b2e1039
             grind)
          | exact superpose b2e1039 b2e38220
          | exact resolve b2e38220 b2e1039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38220
        have b2e38331 : (M.op (τ y) x) = (k (τ y) y) ∨ (k y y) = (k (τ y) y) := by
          first
          | (have i₁ := b2e38313
             have i₂ := b2e94 (τ y)
             grind)
          | exact superpose b2e94 b2e38313
          | exact resolve b2e38313 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38313
        have b2e38346 : (M.op (τ y) x) = (k (τ y) y) ∨ y = (k (τ y) y) := by
          first
          | (have i₁ := b2e38331
             have i₂ := b2e1039
             grind)
          | exact superpose b2e1039 b2e38331
          | exact resolve b2e38331 b2e1039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1039 b2e38331
        have b2e39688 : y ≠ (M.op (τ y) x) ∨ y = (k (τ y) y) := by
          first
          | (have i₁ := b2e38286 y
             have i₂ := b2e94 (τ y)
             grind)
          | exact superpose b2e94 b2e38286
          | (have j0 := b2e38286 y
             grind)
          | exact resolve b2e38286 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e103416 : (τ x) = (M.op (τ x) x) ∨ (M.op (τ x) x) = (k (τ x) y) ∨ (τ x) = (M.op (τ x) x) := by
          first
          | (have i₁ := b2e12824
             have i₂ := b2e491 (τ x) (τ x)
             grind)
          | exact superpose b2e491 b2e12824
          | (have j1 := b2e491 x (τ x)
             grind)
          | exact resolve b2e12824 b2e491
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e491 b2e12824
        have b2e103531 : (M.op (τ x) x) = (k (τ x) y) ∨ (τ x) = (M.op (τ x) x) := by grind
        clear b2e103416
        have b2e133167 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (M.op X0 (σ y))) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e2201 (σ x) (σ y) x
             have i₂ := b2e566
             grind)
          | exact superpose b2e566 b2e2201
          | exact resolve b2e2201 b2e566
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2201
        have b2e134019 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have j0 := b2e133167 X0
             grind)
          | (have r₁ := b2e133167 X0
             have r₂ := b2e571
             grind)
          | exact resolve b2e133167 b2e571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e133167
        have b2e134192 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ (σ y) = (k (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b2e134019 X0
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e134019
          | (have j0 := b2e134019 X0
             grind)
          | exact resolve b2e134019 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134019
        have b2e134274 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (k (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b2e134192 X0
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e134192
          | (have j0 := b2e134192 X0
             grind)
          | exact resolve b2e134192 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e134192
        have b2e134291 : ∀ X0 : G, (σ y) = (k (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have j0 := b2e134274 X0
             grind)
          | (have r₁ := b2e134274 X0
             have r₂ := b2e571
             grind)
          | exact resolve b2e134274 b2e571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134274
        have b2e134451 : ∀ X0 : G, (τ (σ y)) = (k x (τ (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b2e185 x (M.op X0 (σ y))
             have i₂ := b2e134291 X0
             grind)
          | exact superpose b2e134291 b2e185
          | exact resolve b2e185 b2e134291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134291
        have b2e134590 : ∀ X0 : G, y = (k x (τ (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b2e134451 X0
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e134451
          | exact resolve b2e134451 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134451
        have b2e135390 : y = (k x (k (τ x) y)) ∨ x = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e134590 x
             have i₂ := b2e3912 y
             grind)
          | exact superpose b2e3912 b2e134590
          | (have j1 := b2e3912 y
             grind)
          | exact resolve b2e134590 b2e3912
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e135391 : y = (k x (k (τ y) y)) ∨ y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e134590 y
             have i₂ := b2e3980 y
             grind)
          | exact superpose b2e3980 b2e134590
          | (have j1 := b2e3980 y
             grind)
          | exact resolve b2e134590 b2e3980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e136502 : y = (k x (M.op (τ x) x)) ∨ x = (M.op x (σ y)) ∨ y = (k (τ x) y) := by
          first
          | (have i₁ := b2e135390
             have i₂ := b2e32570
             grind)
          | exact superpose b2e32570 b2e135390
          | exact resolve b2e135390 b2e32570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32570 b2e135390
        have b2e136676 : y = (M.op (τ x) x) ∨ x = (M.op x (σ y)) ∨ y = (k (τ x) y) := by
          first
          | (have i₁ := b2e136502
             have i₂ := b2e506 (τ x)
             grind)
          | exact superpose b2e506 b2e136502
          | exact resolve b2e136502 b2e506
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e136502
        have b2e136706 : y = (k (τ x) y) ∨ x = (M.op x (σ y)) := by
          first
          | (have r₁ := b2e136676
             have r₂ := b2e33172
             grind)
          | exact resolve b2e136676 b2e33172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33172 b2e136676
        have b2e137080 : (σ y) = (k x (σ y)) ∨ x = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e27 x y
             have i₂ := b2e136706
             grind)
          | exact superpose b2e136706 b2e27
          | exact resolve b2e27 b2e136706
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e136706
        have b2e137181 : (σ y) = (k x (σ y)) := by
          first
          | (have j1 := b2e15 x (σ y)
             grind)
          | (have r₁ := b2e137080
             have r₂ := b2e15 x (σ y)
             grind)
          | exact resolve b2e137080 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e137080
        have b2e138874 : (τ (σ y)) = (k (τ x) y) := by
          first
          | (have i₁ := b2e32 x y
             have i₂ := b2e137181
             grind)
          | exact superpose b2e137181 b2e32
          | exact resolve b2e32 b2e137181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e138923 : (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op x (σ y)) ∨ x = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e17070 x (σ y)
             have i₂ := b2e137181
             grind)
          | exact superpose b2e137181 b2e17070
          | (have j0 := b2e17070 x (σ y)
             grind)
          | exact resolve b2e17070 b2e137181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e137181
        have b2e138926 : (σ y) = (M.op x (σ y)) ∨ x = (M.op x (σ y)) := by grind
        clear b2e138923
        have b2e138944 : y = (k (τ x) y) := by
          first
          | (have i₁ := b2e138874
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e138874
          | exact resolve b2e138874 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e138874
        have b2e140471 : (τ x) = (M.op (τ x) x) ∨ y = (M.op (τ x) x) := by
          first
          | (have i₁ := b2e103531
             have i₂ := b2e138944
             grind)
          | exact superpose b2e138944 b2e103531
          | exact resolve b2e103531 b2e138944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103531 b2e138944
        have b2e145135 : (M.op x y) = (M.op (σ y) x) ∨ x = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e35 x (σ y)
             have i₂ := b2e138926
             grind)
          | exact superpose b2e138926 b2e35
          | exact resolve b2e35 b2e138926
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e138926
        have b2e145227 : (M.op x y) = (M.op (σ x) x) ∨ x = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e145135
             have i₂ := b2e578 x
             grind)
          | exact superpose b2e578 b2e145135
          | exact resolve b2e145135 b2e578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e145135
        have b2e145249 : x = (M.op (σ x) x) ∨ x = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e145227
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e145227
          | exact resolve b2e145227 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e145227
        have b2e150024 : (τ x) = (k x (τ x)) ∨ y = (M.op (τ x) x) := by
          first
          | (have i₁ := b2e506 (τ x)
             have i₂ := b2e140471
             grind)
          | exact superpose b2e140471 b2e506
          | exact resolve b2e506 b2e140471
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e150099 : y ≠ (τ x) ∨ y = (M.op (τ x) x) := by grind
        clear b2e140471
        have b2e159285 : y = (k x (M.op (τ y) x)) ∨ y = (M.op y (σ y)) ∨ y = (k (τ y) y) := by
          first
          | (have i₁ := b2e135391
             have i₂ := b2e38346
             grind)
          | exact superpose b2e38346 b2e135391
          | exact resolve b2e135391 b2e38346
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38346 b2e135391
        have b2e159461 : y = (M.op (τ y) x) ∨ y = (M.op y (σ y)) ∨ y = (k (τ y) y) := by
          first
          | (have i₁ := b2e159285
             have i₂ := b2e506 (τ y)
             grind)
          | exact superpose b2e506 b2e159285
          | exact resolve b2e159285 b2e506
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e506 b2e159285
        have b2e159490 : y = (k (τ y) y) ∨ y = (M.op y (σ y)) := by
          first
          | (have r₁ := b2e159461
             have r₂ := b2e39688
             grind)
          | exact resolve b2e159461 b2e39688
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39688 b2e159461
        have b2e159611 : (σ y) = (k y (σ y)) ∨ y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e27 y y
             have i₂ := b2e159490
             grind)
          | exact superpose b2e159490 b2e27
          | exact resolve b2e27 b2e159490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159490
        have b2e159716 : (σ y) = (k y (σ y)) := by
          first
          | (have j1 := b2e15 y (σ y)
             grind)
          | (have r₁ := b2e159611
             have r₂ := b2e15 y (σ y)
             grind)
          | exact resolve b2e159611 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159611
        have b2e159995 : (σ y) = (M.op y (σ y)) ∨ (σ y) = (M.op y (σ y)) ∨ y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e17070 y (σ y)
             have i₂ := b2e159716
             grind)
          | exact superpose b2e159716 b2e17070
          | (have j0 := b2e17070 y (σ y)
             grind)
          | exact resolve b2e17070 b2e159716
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159716
        have b2e159998 : (σ y) = (M.op y (σ y)) ∨ y = (M.op y (σ y)) := by grind
        clear b2e159995
        have b2e164125 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ y = (M.op y (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e39 y (σ y) X0
             have i₂ := b2e159998
             grind)
          | exact superpose b2e159998 b2e39
          | exact resolve b2e39 b2e159998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159998
        have b2e164224 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ y = (M.op y (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e164125 X0
             have i₂ := b2e578 X0
             grind)
          | exact superpose b2e578 b2e164125
          | exact resolve b2e164125 b2e578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e578 b2e164125
        have b2e174200 : y = (M.op y (σ y)) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e1531
             have i₂ := b2e164224 (σ x)
             grind)
          | exact superpose b2e164224 b2e1531
          | exact resolve b2e1531 b2e164224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e164224
        have b2e174604 : (M.op x y) = (M.op x (σ y)) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e33 (σ y) y
             have i₂ := b2e174200
             grind)
          | exact superpose b2e174200 b2e33
          | exact resolve b2e33 b2e174200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e174200
        have b2e174665 : (σ x) = (M.op y (σ x)) ∨ x = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e174604
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e174604
          | exact resolve b2e174604 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174604
        have b2e175369 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ x = (M.op x (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e39 y (σ x) X0
             have i₂ := b2e174665
             grind)
          | exact superpose b2e174665 b2e39
          | exact resolve b2e39 b2e174665
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e174665
        have b2e177311 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (M.op X0 (σ x))) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e4820 (σ x) x
             have i₂ := b2e1531
             grind)
          | exact superpose b2e1531 b2e4820
          | (have r₁ := b2e4820 (σ x) x
             have r₂ := b2e1531
             grind)
          | exact resolve b2e4820 b2e1531
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1531 b2e4820
        have b2e177315 : ∀ X0 : G, (σ x) = (k (σ y) (M.op X0 (σ x))) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have j0 := b2e177311 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177311
        have b2e177319 : ∀ X0 : G, (σ x) = (k (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have j0 := b2e177315 X0
             grind)
          | (have r₁ := b2e177315 X0
             have r₂ := b2e571
             grind)
          | exact resolve b2e177315 b2e571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177315
        have b2e177392 : ∀ X0 : G, (τ (σ x)) = (k y (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b2e185 y (M.op X0 (σ x))
             have i₂ := b2e177319 X0
             grind)
          | exact superpose b2e177319 b2e185
          | exact resolve b2e185 b2e177319
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e185 b2e177319
        have b2e177426 : ∀ X0 : G, x = (k y (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b2e177392 X0
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e177392
          | exact resolve b2e177392 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177392
        have b2e177547 : x = (k y (k (τ x) x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b2e177426 x
             have i₂ := b2e3912 x
             grind)
          | exact superpose b2e3912 b2e177426
          | (have j1 := b2e3912 x
             grind)
          | exact resolve b2e177426 b2e3912
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3912
        have b2e177548 : x = (k y (k (τ y) x)) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e177426 y
             have i₂ := b2e3980 x
             grind)
          | exact superpose b2e3980 b2e177426
          | (have j1 := b2e3980 x
             grind)
          | exact resolve b2e177426 b2e3980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3980 b2e177426
        have b2e177684 : x = (k y (M.op (τ x) x)) ∨ x = (M.op x (σ x)) ∨ x = (k (τ x) x) := by
          first
          | (have i₁ := b2e177547
             have i₂ := b2e13552 x
             grind)
          | exact superpose b2e13552 b2e177547
          | (have j1 := b2e13552 x
             grind)
          | exact resolve b2e177547 b2e13552
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13552 b2e177547
        have b2e177728 : x = (M.op (τ x) x) ∨ x = (M.op x (σ x)) ∨ x = (k (τ x) x) := by
          first
          | (have i₁ := b2e177684
             have i₂ := b2e1164 (τ x)
             grind)
          | exact superpose b2e1164 b2e177684
          | exact resolve b2e177684 b2e1164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177684
        have b2e177731 : x = (k (τ x) x) ∨ x = (M.op x (σ x)) := by
          first
          | (have j1 := b2e32519 x
             grind)
          | (have r₁ := b2e177728
             have r₂ := b2e32519 x
             grind)
          | exact resolve b2e177728 b2e32519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32519 b2e177728
        have b2e177757 : (σ x) = (k x (σ x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b2e27 x x
             have i₂ := b2e177731
             grind)
          | exact superpose b2e177731 b2e27
          | exact resolve b2e27 b2e177731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177731
        have b2e177785 : (σ x) = (k x (σ x)) := by
          first
          | (have j1 := b2e15 x (σ x)
             grind)
          | (have r₁ := b2e177757
             have r₂ := b2e15 x (σ x)
             grind)
          | exact resolve b2e177757 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177757
        have b2e177843 : (τ (σ x)) = (k (τ x) x) := by
          first
          | (have i₁ := b2e32 x x
             have i₂ := b2e177785
             grind)
          | exact superpose b2e177785 b2e32
          | exact resolve b2e32 b2e177785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177785
        have b2e177884 : x = (k (τ x) x) := by
          first
          | (have i₁ := b2e177843
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e177843
          | exact resolve b2e177843 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177843
        have b2e178062 : x = (M.op (τ x) x) ∨ x = (M.op (τ x) x) ∨ (τ x) = (M.op (τ x) x) := by
          first
          | (have i₁ := b2e17070 (τ x) x
             have i₂ := b2e177884
             grind)
          | exact superpose b2e177884 b2e17070
          | (have j0 := b2e17070 (τ x) x
             grind)
          | exact resolve b2e17070 b2e177884
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17070 b2e177884
        have b2e178064 : (τ x) = (M.op (τ x) x) ∨ x = (M.op (τ x) x) := by grind
        clear b2e178062
        have b2e180279 : x = (k y (M.op (τ y) x)) ∨ y = (M.op y (σ x)) ∨ x = (k (τ y) x) := by
          first
          | (have i₁ := b2e177548
             have i₂ := b2e13808 x
             grind)
          | exact superpose b2e13808 b2e177548
          | (have j1 := b2e13808 x
             grind)
          | exact resolve b2e177548 b2e13808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13808 b2e177548
        have b2e180323 : x = (M.op (τ y) x) ∨ y = (M.op y (σ x)) ∨ x = (k (τ y) x) := by
          first
          | (have i₁ := b2e180279
             have i₂ := b2e1164 (τ y)
             grind)
          | exact superpose b2e1164 b2e180279
          | exact resolve b2e180279 b2e1164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1164 b2e180279
        have b2e180326 : x = (k (τ y) x) ∨ y = (M.op y (σ x)) := by
          first
          | (have j1 := b2e38286 x
             grind)
          | (have r₁ := b2e180323
             have r₂ := b2e38286 x
             grind)
          | exact resolve b2e180323 b2e38286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38286 b2e180323
        have b2e180357 : (σ x) = (k y (σ x)) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e27 y x
             have i₂ := b2e180326
             grind)
          | exact superpose b2e180326 b2e27
          | exact resolve b2e27 b2e180326
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e180326
        have b2e180385 : (σ x) = (k y (σ x)) := by
          first
          | (have j1 := b2e15 y (σ x)
             grind)
          | (have r₁ := b2e180357
             have r₂ := b2e15 y (σ x)
             grind)
          | exact resolve b2e180357 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180357
        have b2e180440 : (τ (σ x)) = (k (τ y) x) := by
          first
          | (have i₁ := b2e32 y x
             have i₂ := b2e180385
             grind)
          | exact superpose b2e180385 b2e32
          | exact resolve b2e32 b2e180385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e180444 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ (σ x) = (M.op y y) ∨ y = (M.op y (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e13340 y x X0
             have i₂ := b2e180385
             grind)
          | exact superpose b2e180385 b2e13340
          | (have j0 := b2e13340 y x x
             grind)
          | exact resolve b2e13340 b2e180385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13340 b2e180385
        have b2e180483 : ∀ X0 : G, (σ x) = (M.op y x) ∨ (M.op (σ x) X0) = (M.op y X0) ∨ y = (M.op y (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e180444 X0
             have i₂ := b2e94 y
             grind)
          | exact superpose b2e94 b2e180444
          | (have j0 := b2e180444 X0
             grind)
          | exact resolve b2e180444 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94 b2e180444
        have b2e180487 : x = (k (τ y) x) := by
          first
          | (have i₁ := b2e180440
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e180440
          | exact resolve b2e180440 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180440
        have b2e180501 : ∀ X0 : G, y = (σ x) ∨ (M.op (σ x) X0) = (M.op y X0) ∨ y = (M.op y (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e180483 X0
             have i₂ := b2e1094
             grind)
          | exact superpose b2e1094 b2e180483
          | (have j0 := b2e180483 X0
             grind)
          | exact resolve b2e180483 b2e1094
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180483
        have b2e180641 : ∀ X0 : G, (σ x) ≠ (σ (τ y)) ∨ (M.op (σ x) X0) = (M.op (σ (τ y)) X0) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e10401 (τ y) x X0
             have i₂ := b2e180487
             grind)
          | exact superpose b2e180487 b2e10401
          | (have j0 := b2e10401 (τ y) x X0
             grind)
          | exact resolve b2e10401 b2e180487
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10401 b2e180487
        have b2e180652 : ∀ X0 : G, y ≠ (σ x) ∨ (M.op (σ x) X0) = (M.op (σ (τ y)) X0) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e180641 X0
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e180641
          | (have j0 := b2e180641 X0
             grind)
          | exact resolve b2e180641 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180641
        have b2e180667 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ y ≠ (σ x) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e180652 X0
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e180652
          | exact resolve b2e180652 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180652
        have b2e180672 : ∀ X0 : G, y = (M.op y (σ x)) ∨ (M.op (σ x) X0) = (M.op y X0) ∨ y ≠ (σ x) := by
          intro X0
          first
          | (have i₁ := b2e180667 X0
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e180667
          | (have j0 := b2e180667 X0
             grind)
          | exact resolve b2e180667 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180667
        have b2e180677 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ y = (M.op y (σ x)) := by
          intro X0
          first
          | (have j0 := b2e180672 X0
             have j1 := b2e180501 X0
             grind)
          | (have r₁ := b2e180672 X0
             have r₂ := b2e180501 X0
             grind)
          | exact resolve b2e180672 b2e180501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180501 b2e180672
        have b2e183101 : (σ y) = (M.op y (σ y)) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e566
             have i₂ := b2e180677 (σ y)
             grind)
          | exact superpose b2e180677 b2e566
          | exact resolve b2e566 b2e180677
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180677
        have b2e185110 : x = (M.op y x) ∨ x = (M.op x (σ y)) ∨ x = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e145249
             have i₂ := b2e175369 x
             grind)
          | exact superpose b2e175369 b2e145249
          | exact resolve b2e145249 b2e175369
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e145249 b2e175369
        have b2e185226 : x = (M.op y x) ∨ x = (M.op x (σ y)) := by grind
        clear b2e185110
        have b2e185244 : x = (M.op x (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e185226
             have i₂ := b2e1094
             grind)
          | exact superpose b2e1094 b2e185226
          | exact resolve b2e185226 b2e1094
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e185226
        have b2e185370 : y = (k x (τ x)) ∨ x = y := by
          first
          | (have i₁ := b2e134590 x
             have i₂ := b2e185244
             grind)
          | exact superpose b2e185244 b2e134590
          | exact resolve b2e134590 b2e185244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134590 b2e185244
        have b2e185743 : y = (τ x) ∨ y = (M.op (τ x) x) ∨ x = y := by
          first
          | (have i₁ := b2e150024
             have i₂ := b2e185370
             grind)
          | exact superpose b2e185370 b2e150024
          | exact resolve b2e150024 b2e185370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150024 b2e185370
        have b2e185792 : y = (M.op (τ x) x) ∨ x = y := by
          first
          | (have r₁ := b2e185743
             have r₂ := b2e150099
             grind)
          | exact resolve b2e185743 b2e150099
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150099 b2e185743
        have b2e185852 : y = (τ x) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e178064
             have i₂ := b2e185792
             grind)
          | exact superpose b2e185792 b2e178064
          | exact resolve b2e178064 b2e185792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e178064 b2e185792
        have b2e185978 : y = (τ x) ∨ x = y := by grind
        clear b2e185852
        have b2e186112 : x = (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e14 x
             have i₂ := b2e185978
             grind)
          | exact superpose b2e185978 b2e14
          | exact resolve b2e14 b2e185978
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e185978
        have b2e186306 : x = (M.op (σ x) x) ∨ x = y := by
          first
          | (have i₁ := b2e566
             have i₂ := b2e186112
             grind)
          | exact superpose b2e186112 b2e566
          | exact resolve b2e566 b2e186112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e566
        have b2e186307 : x ≠ (σ x) ∨ x = y := by
          first
          | (have i₁ := b2e571
             have i₂ := b2e186112
             grind)
          | exact superpose b2e186112 b2e571
          | exact resolve b2e571 b2e186112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e186363 : x = (M.op y x) ∨ y = (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e183101
             have i₂ := b2e186112
             grind)
          | exact superpose b2e186112 b2e183101
          | exact resolve b2e183101 b2e186112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e183101
        have b2e186514 : x = y ∨ y = (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e186363
             have i₂ := b2e1094
             grind)
          | exact superpose b2e1094 b2e186363
          | exact resolve b2e186363 b2e1094
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1094 b2e186363
        have b2e186515 : y = (M.op y (σ x)) ∨ x = y := by grind
        clear b2e186514
        have b2e186590 : x ≠ (σ y) ∨ x = (k (σ x) y) ∨ x = (σ x) ∨ x = y := by
          first
          | (have i₁ := b2e4883
             have i₂ := b2e186306
             grind)
          | exact superpose b2e186306 b2e4883
          | exact resolve b2e4883 b2e186306
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4883 b2e186306
        have b2e186749 : x ≠ (σ y) ∨ x = (k (σ x) y) ∨ x = y := by
          first
          | (have r₁ := b2e186590
             have r₂ := b2e186307
             grind)
          | exact resolve b2e186590 b2e186307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e186307 b2e186590
        have b2e186757 : x = (k (σ x) y) ∨ x = y := by
          first
          | (have r₁ := b2e186749
             have r₂ := b2e186112
             grind)
          | exact resolve b2e186749 b2e186112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e186112 b2e186749
        have b2e186826 : y = (k (σ x) y) ∨ x = y := by
          first
          | (have i₁ := b2e1570 y
             have i₂ := b2e186515
             grind)
          | exact superpose b2e186515 b2e1570
          | exact resolve b2e1570 b2e186515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1570 b2e186515
        have b2e187760 : x = y ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e186757
             have i₂ := b2e186826
             grind)
          | exact superpose b2e186826 b2e186757
          | exact resolve b2e186757 b2e186826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e186757 b2e186826
        have b2e187797 : x = y := by grind
        clear b2e187760
        have b2e187903 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e571
             have i₂ := b2e187797
             grind)
          | exact superpose b2e187797 b2e571
          | exact resolve b2e571 b2e187797
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e571 b2e187797
        have b2e188074 : False := by grind
        exact b2e188074
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e27 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e26
        have b3e28 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e27
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e27
          | exact resolve b3e27 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e33 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e13
          | exact resolve b3e13 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : y = (k x y) := by
          first
          | (have i₁ := b3e33
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e33
          | exact resolve b3e33 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e46 : x = (k x y) ∨ x = (M.op x y) := by grind
        have b3e48 : x = (k x y) := by
          first
          | (have r₁ := b3e46
             have r₂ := b3e20
             grind)
          | exact resolve b3e46 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e50 : x = y := by
          first
          | (have i₁ := b3e34
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e34
          | exact resolve b3e34 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e51 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e28
          | exact resolve b3e28 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e48
        have b3e77 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e24
          | exact resolve b3e24 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e50
        have b3e81 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e77
          | exact resolve b3e77 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e83 : False := by grind
        exact b3e83
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e38 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
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
          have b4e42 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e40 x X1 X2 X3 x
               have i₂ := b4e13 X2 X1 x x
               grind)
            | exact superpose b4e13 b4e40
            | exact resolve b4e40 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e103 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 y X2 (M.op X0 x)
               have i₂ := b4e38 X0 x
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e107 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b4e103 x X1 x
               have i₂ := b4e13 X1 x x x
               grind)
            | exact superpose b4e13 b4e103
            | exact resolve b4e103 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103
          have b4e122 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e42 (σ x) X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e42
            | exact resolve b4e42 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e381 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e122 (σ x)
               grind)
            | exact superpose b4e122 b4e20
            | exact resolve b4e20 b4e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122
          have b4e387 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e381
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e381
            | exact resolve b4e381 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e381
          have b4e398 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e387
               have i₂ := b4e107 x
               grind)
            | exact superpose b4e107 b4e387
            | exact resolve b4e387 b4e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e107 b4e387
          have b4e402 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e398
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e398
            | exact resolve b4e398 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e398
          have b4e403 : False := by grind
          exact b4e403
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
          have b5e54 : x = (k x y) := by
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
          have b5e620 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e69 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e621 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e620
               have r₂ := b5e23
               grind)
            | exact resolve b5e620 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e620
          have b5e622 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e621
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e621
            | exact resolve b5e621 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e621
          have b5e623 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e622
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e622
            | exact resolve b5e622 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e622
          have b5e624 : False := by grind
          exact b5e624
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e26 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e25
        have b6e27 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e26
          | exact resolve b6e26 b6e18
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
        have b6e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b6e32 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e27
             grind)
          | exact superpose b6e27 b6e13
          | exact resolve b6e13 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e33 : y = (k x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e32
          | exact resolve b6e32 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e36 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (σ x) X0 (σ y) X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
          intro X0 X1 X2 X3 X5
          first
          | (have i₁ := b6e12 (M.op X0 X2) X3 (M.op x X1) X5
             have i₂ := b6e12 X0 X1 X2 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
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
        have b6e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X3 X1) = (k (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e15 (M.op X0 X2) (M.op X3 X1)
             have i₂ := b6e12 X0 X1 X2 X3
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X0 X2) (M.op X3 X1)
             grind)
          | (have r₁ := b6e15 (M.op X0 X1) (M.op X3 X1)
             have r₂ := b6e12 X0 X1 X1 X3
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b6e39 x X1 X2 X3 x
             have i₂ := b6e12 X2 X1 x x
             grind)
          | exact superpose b6e12 b6e39
          | exact resolve b6e39 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e42 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b6e37 X0 x X2 X3 x
             have i₂ := b6e12 X0 X3 x x
             grind)
          | exact superpose b6e12 b6e37
          | exact resolve b6e37 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e44 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e41 (σ y) X0 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e41
          | exact resolve b6e41 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b6e62 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e33
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e33 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e64 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e41 X2 X1 X2
             have i₂ := b6e17 X2 X0
             grind)
          | (have i₁ := b6e41 X1 X2 x
             have i₂ := b6e17 X0 (M.op x X1)
             grind)
          | exact superpose b6e17 b6e41
          | (have j1 := b6e17 X2 X0
             grind)
          | exact resolve b6e41 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e66 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X2 X1 X3
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e12 X0 X1 X2 X3
             have i₂ := b6e17 X0 (M.op X0 X2)
             grind)
          | exact superpose b6e17 b6e12
          | (have j1 := b6e17 X1 X0
             grind)
          | exact resolve b6e12 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e74 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e66 X0 X1 X2 x
             have i₂ := b6e41 X2 X0 x
             grind)
          | exact superpose b6e41 b6e66
          | (have j0 := b6e66 X0 X1 X2 x
             grind)
          | exact resolve b6e66 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e77 : y = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e62
             have r₂ := b6e21
             grind)
          | exact resolve b6e62 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e84 : y = (M.op x y) := by
          first
          | (have r₁ := b6e77
             have r₂ := b6e20
             grind)
          | exact resolve b6e77 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e91 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e84
             grind)
          | exact superpose b6e84 b6e20
          | exact resolve b6e20 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e93 : ∀ X0 X1 : G, (M.op x X0) = (M.op y (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 x X0 y X1
             have i₂ := b6e84
             grind)
          | exact superpose b6e84 b6e12
          | exact resolve b6e12 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e95 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e93 X0 x
             have i₂ := b6e41 X0 y x
             grind)
          | exact superpose b6e41 b6e93
          | exact resolve b6e93 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e93
        have b6e108 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X0 X2) X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 (M.op X0 X2) X1
             have i₂ := b6e42 X0 X2 X1
             grind)
          | exact superpose b6e42 b6e15
          | (have j0 := b6e15 (M.op X0 X2) X1
             grind)
          | (have r₁ := b6e15 (M.op X0 x) x
             have r₂ := b6e42 X0 x x
             grind)
          | exact resolve b6e15 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e127 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e28 X0 X1
             have i₂ := b6e17 (τ X0) X1
             grind)
          | exact superpose b6e17 b6e28
          | (have j1 := b6e17 (τ X0) X1
             grind)
          | exact resolve b6e28 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e128 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e18 X2 (k (τ X0) X1)
             have i₂ := b6e28 X0 X1
             grind)
          | exact superpose b6e28 b6e18
          | exact resolve b6e18 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e130 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e28 X0 X1
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e134 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X1 X0
             have i₂ := b6e17 X0 (τ X1)
             grind)
          | exact superpose b6e17 b6e29
          | (have j1 := b6e17 X0 (τ X1)
             grind)
          | exact resolve b6e29 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e139 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e29 X1 X0
             grind)
          | exact superpose b6e29 b6e13
          | exact resolve b6e13 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e153 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e36 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e36
          | exact resolve b6e36 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e171 : y = (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) := by grind
        have b6e174 : y = (k y y) ∨ y = (M.op y (M.op x y)) := by
          first
          | (have i₁ := b6e171
             have i₂ := b6e84
             grind)
          | exact superpose b6e84 b6e171
          | exact resolve b6e171 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e171
        have b6e178 : y = (M.op y y) ∨ y = (k y y) := by
          first
          | (have i₁ := b6e174
             have i₂ := b6e41 y y x
             grind)
          | exact superpose b6e41 b6e174
          | exact resolve b6e174 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e174
        have b6e179 : y = (k y y) := by
          first
          | (have j1 := b6e15 y y
             grind)
          | (have r₁ := b6e178
             have r₂ := b6e15 y y
             grind)
          | exact resolve b6e178 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e178
        have b6e231 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e153
             grind)
          | exact superpose b6e153 b6e15
          | (have j0 := b6e15 (σ x) (σ x)
             grind)
          | (have r₁ := b6e15 (σ x) (σ x)
             have r₂ := b6e153
             grind)
          | exact resolve b6e15 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e236 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b6e231
        have b6e237 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e236
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e236
          | exact resolve b6e236 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e236
        have b6e258 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X2 X1) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e40 X2 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e280 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e237
             grind)
          | exact superpose b6e237 b6e13
          | exact resolve b6e13 b6e237
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e237
        have b6e282 : x = (k x x) := by
          first
          | (have i₁ := b6e280
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e280
          | exact resolve b6e280 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e280
        have b6e325 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X2 ∨ (M.op X1 X2) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e17 X1 X2
             have i₂ := b6e74 X1 X0 X1
             grind)
          | (have i₁ := b6e17 X2 X1
             have i₂ := b6e74 X0 X2 X2
             grind)
          | exact superpose b6e74 b6e17
          | (have j0 := b6e17 X1 X2
             have j1 := b6e74 X2 X1 X2
             grind)
          | exact resolve b6e17 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e329 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 (M.op X2 X3)) = (k X0 (M.op X2 X3)) ∨ (M.op X0 (M.op X2 X3)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e42 X2 X3 X1
             have i₂ := b6e74 (M.op X2 X3) X0 X1
             grind)
          | (have i₁ := b6e42 X0 X2 X2
             have i₂ := b6e74 X0 (M.op X0 X2) X2
             grind)
          | exact superpose b6e74 b6e42
          | (have j1 := b6e74 (M.op X2 X3) X0 X2
             grind)
          | exact resolve b6e42 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e371 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 (M.op X2 X3)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e329 X0 X1 X2 X3
             have i₂ := b6e41 X3 X0 X2
             grind)
          | exact superpose b6e41 b6e329
          | (have j0 := b6e329 X0 X1 X2 X3
             grind)
          | exact resolve b6e329 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e329
        have b6e397 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X3) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e371 X0 X1 X2 X3
             have i₂ := b6e41 X3 X0 X2
             grind)
          | exact superpose b6e41 b6e371
          | (have j0 := b6e371 X0 X1 X2 X3
             grind)
          | exact resolve b6e371 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e371
        have b6e419 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e282
             grind)
          | exact superpose b6e282 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e420 : x = (M.op x x) := by grind
        clear b6e419
        have b6e555 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ X1)) ∨ (M.op (σ X0) X2) = (k (σ X0) X2) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e74 X2 (σ X0) (σ X1)
             have i₂ := b6e61 X0 X1
             grind)
          | exact superpose b6e61 b6e74
          | (have j0 := b6e74 X2 (σ X0) X2
             have j1 := b6e61 X0 X1
             grind)
          | exact resolve b6e74 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e579 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e61 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e580 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e581 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e579 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e579
        have b6e639 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e130 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e130
          | exact resolve b6e130 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e642 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e130 X2 (k (τ X0) X1)
             have i₂ := b6e28 X0 X1
             grind)
          | exact superpose b6e28 b6e130
          | exact resolve b6e130 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e746 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e258 X0 (σ x) (σ x)
             have i₂ := b6e153
             grind)
          | exact superpose b6e153 b6e258
          | exact resolve b6e258 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e854 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k (M.op x X0) x) := by
          intro X0
          first
          | (have i₁ := b6e108 x x X0
             have i₂ := b6e420
             grind)
          | exact superpose b6e420 b6e108
          | (have j0 := b6e108 x x X0
             grind)
          | exact resolve b6e108 b6e420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e872 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e108 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108
        have b6e910 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e130 (M.op X1 (σ X0)) X0
             have i₂ := b6e872 X1 (σ X0)
             grind)
          | exact superpose b6e872 b6e130
          | exact resolve b6e130 b6e872
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e911 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (τ X0))) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X0 (M.op X1 (τ X0))
             have i₂ := b6e872 X1 (τ X0)
             grind)
          | exact superpose b6e872 b6e29
          | exact resolve b6e29 b6e872
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e912 : ∀ X0 X1 : G, (k (σ (M.op X1 (τ X0))) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e911 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e911
          | exact resolve b6e911 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e911
        have b6e913 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e910 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e910
          | exact resolve b6e910 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e910
        have b6e1335 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e581 (M.op X0 X1)
             have i₂ := b6e258 X0 X1 X0
             grind)
          | exact superpose b6e258 b6e581
          | (have j0 := b6e581 (M.op X0 X1)
             grind)
          | exact resolve b6e581 b6e258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1338 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e581 y
             have i₂ := b6e179
             grind)
          | exact superpose b6e179 b6e581
          | (have j0 := b6e581 y
             grind)
          | exact resolve b6e581 b6e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1341 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e581 (τ X0)
             have i₂ := b6e29 X0 (τ X0)
             grind)
          | exact superpose b6e29 b6e581
          | (have j0 := b6e581 (τ X0)
             grind)
          | exact resolve b6e581 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e1344 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e1338
        have b6e1346 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have j0 := b6e1335 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1335
        have b6e1348 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e1341 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1341
          | (have j0 := b6e1341 X0
             grind)
          | exact resolve b6e1341 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1341
        have b6e1350 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e1344
             have i₂ := b6e44 (σ y)
             grind)
          | exact superpose b6e44 b6e1344
          | exact resolve b6e1344 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1344
        have b6e1351 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1348 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1348
          | (have j0 := b6e1348 X0
             grind)
          | exact resolve b6e1348 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1348
        have b6e1356 : x = (k (τ (σ y)) x) := by
          first
          | (have i₁ := b6e913 x (σ y)
             have i₂ := b6e1350
             grind)
          | exact superpose b6e1350 b6e913
          | exact resolve b6e913 b6e1350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e913
        have b6e1372 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e258 X0 (σ x) (σ y)
             have i₂ := b6e1350
             grind)
          | exact superpose b6e1350 b6e258
          | exact resolve b6e258 b6e1350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1350
        have b6e1380 : x = (k y x) := by
          first
          | (have i₁ := b6e1356
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1356
          | exact resolve b6e1356 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1356
        have b6e1699 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e64 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1929 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op (M.op X2 X3) X4) = (k (M.op X2 X3) (M.op X0 X4)) ∨ (M.op X2 X3) = (M.op (M.op X2 X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e42 X2 X3 X1
             have i₂ := b6e397 (M.op X2 X3) X1 X0 X4
             grind)
          | (have i₁ := b6e42 X0 X2 X1
             have i₂ := b6e397 X0 X1 (M.op X0 X2) X3
             grind)
          | exact superpose b6e397 b6e42
          | (have j1 := b6e397 (M.op X2 X3) X1 X0 X4
             grind)
          | exact resolve b6e42 b6e397
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e397
        have b6e1980 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X4) = (k (M.op X2 X3) (M.op X0 X4)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X3) = (M.op (M.op X2 X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e1929 X0 X1 X2 X3 X4
             have i₂ := b6e42 X2 X3 X4
             grind)
          | exact superpose b6e42 b6e1929
          | (have j0 := b6e1929 X0 X1 X2 X3 X4
             grind)
          | exact resolve b6e1929 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1929
        have b6e2014 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X4) = (k (M.op X2 X3) (M.op X0 X4)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X3) = (M.op X2 X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e1980 X0 X1 X2 X3 X4
             have i₂ := b6e42 X2 X3 X4
             grind)
          | exact superpose b6e42 b6e1980
          | (have j0 := b6e1980 X0 X1 X2 X3 X4
             grind)
          | exact resolve b6e1980 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1980
        have b6e2101 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e134 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e134
          | exact resolve b6e134 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2145 : ∀ X0 X1 X2 : G, (τ X0) = (k (M.op X2 X1) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 (τ X0)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e258 X0 X0 X2
             have i₂ := b6e134 X0 X1
             grind)
          | exact superpose b6e134 b6e258
          | (have j1 := b6e134 X1 X0
             grind)
          | exact resolve b6e258 b6e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e2198 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e2101 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e2101
          | (have j0 := b6e2101 X0 X1
             grind)
          | exact resolve b6e2101 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2101
        have b6e2329 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e1351 (τ X0)
             have i₂ := b6e639 X0 X0
             grind)
          | exact superpose b6e639 b6e1351
          | (have j0 := b6e1351 (τ X0)
             grind)
          | exact resolve b6e1351 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1351
        have b6e2816 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        clear b6e580
        have b6e2862 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e2816 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2816
        have b6e2879 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e2862 X0
             have i₂ := b6e41 X0 X0 X0
             grind)
          | exact superpose b6e41 b6e2862
          | (have j0 := b6e2862 X0
             grind)
          | exact resolve b6e2862 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2862
        have b6e3129 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b6e139 x (M.op X0 (σ x))
             have i₂ := b6e746 X0
             grind)
          | exact superpose b6e746 b6e139
          | exact resolve b6e139 b6e746
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e746
        have b6e3973 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k y (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b6e139 y (M.op X0 (σ x))
             have i₂ := b6e1372 X0
             grind)
          | exact superpose b6e1372 b6e139
          | exact resolve b6e139 b6e1372
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1372
        have b6e6189 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X1))) = (k (σ (M.op X0 X1)) (M.op X2 (σ (M.op X0 X1)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e258 X2 (σ (M.op X0 X1)) (σ (M.op X0 X1))
             have i₂ := b6e1346 X0 X1
             grind)
          | exact superpose b6e1346 b6e258
          | exact resolve b6e258 b6e1346
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e8490 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e325 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e325
        have b6e8492 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e8490 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8490
        have b6e8493 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e8492 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8492
        have b6e8724 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e639 X0 X0
             have i₂ := b6e8493 (τ X0)
             grind)
          | exact superpose b6e8493 b6e639
          | (have j1 := b6e8493 (τ X0)
             grind)
          | exact resolve b6e639 b6e8493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8493
        have b6e15154 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e2329 (M.op X0 X1)
             have i₂ := b6e258 X0 X1 X0
             grind)
          | exact superpose b6e258 b6e2329
          | (have j0 := b6e2329 (M.op X0 X1)
             grind)
          | exact resolve b6e2329 b6e258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e15160 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
          first
          | (have i₁ := b6e2329 x
             have i₂ := b6e282
             grind)
          | exact superpose b6e282 b6e2329
          | (have j0 := b6e2329 x
             grind)
          | exact resolve b6e2329 b6e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e282
        have b6e15161 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
          first
          | (have i₁ := b6e2329 y
             have i₂ := b6e179
             grind)
          | exact superpose b6e179 b6e2329
          | (have j0 := b6e2329 y
             grind)
          | exact resolve b6e2329 b6e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e179
        have b6e15169 : (τ y) = (M.op (τ y) (τ y)) := by grind
        clear b6e15161
        have b6e15170 : (τ x) = (M.op (τ x) (τ x)) := by grind
        clear b6e15160
        have b6e15172 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have j0 := b6e15154 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15154
        have b6e16382 : ∀ X0 : G, (τ y) = (M.op (τ y) X0) ∨ (k (τ y) X0) = (M.op (τ y) X0) ∨ (τ y) = (M.op (τ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e64 X0 (τ y) (τ y)
             have i₂ := b6e15169
             grind)
          | exact superpose b6e15169 b6e64
          | (have j0 := b6e64 X0 x (τ y)
             grind)
          | exact resolve b6e64 b6e15169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e16411 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) ∨ (τ y) = (M.op (τ y) X0) := by
          intro X0
          first
          | (have j0 := b6e16382 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16382
        have b6e38758 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e581 X1
             have i₂ := b6e555 X1 X1 X0
             grind)
          | exact superpose b6e555 b6e581
          | (have j0 := b6e581 X1
             have j1 := b6e555 X1 X1 X0
             grind)
          | exact resolve b6e581 b6e555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e555 b6e581
        have b6e39502 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b6e38758 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38758
        have b6e39857 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b6e39502 X0 X1
             have j1 := b6e1699 (σ X1) X0
             grind)
          | (have r₁ := b6e39502 (σ X1) X1
             have r₂ := b6e1699 (σ X1) (σ X1)
             grind)
          | (have r₁ := b6e39502 X0 X1
             have r₂ := b6e1699 (σ X1) X1
             grind)
          | (have r₁ := b6e39502 (σ X1) X1
             have r₂ := b6e1699 (σ X1) X1
             grind)
          | exact resolve b6e39502 b6e1699
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39502
        have b6e51085 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e1699 x X0
             have i₂ := b6e420
             grind)
          | exact superpose b6e420 b6e1699
          | (have j0 := b6e1699 x X0
             grind)
          | (have r₁ := b6e1699 x x
             have r₂ := b6e420
             grind)
          | exact resolve b6e1699 b6e420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e51086 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k y X0) = (M.op y X0) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e1699 y X0
             have i₂ := b6e95 y
             grind)
          | exact superpose b6e95 b6e1699
          | (have j0 := b6e1699 y X0
             grind)
          | exact resolve b6e1699 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1699
        have b6e51087 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b6e51085 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51085
        have b6e51107 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b6e51086 X0
             grind)
          | (have r₁ := b6e51086 X0
             have r₂ := b6e84
             grind)
          | exact resolve b6e51086 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84 b6e51086
        have b6e51124 : ∀ X0 : G, (k y X0) = (M.op x X0) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e51107 X0
             have i₂ := b6e95 X0
             grind)
          | exact superpose b6e95 b6e51107
          | (have j0 := b6e51107 X0
             grind)
          | exact resolve b6e51107 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51107
        have b6e51133 : ∀ X0 : G, (k y X0) = (M.op x X0) ∨ y = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e51124 X0
             have i₂ := b6e95 X0
             grind)
          | exact superpose b6e95 b6e51124
          | (have j0 := b6e51124 X0
             grind)
          | exact resolve b6e51124 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95 b6e51124
        have b6e51232 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ y) X0) ∨ y = (M.op x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e130 y X0
             have i₂ := b6e51133 (σ X0)
             grind)
          | exact superpose b6e51133 b6e130
          | (have j1 := b6e51133 (σ X0)
             grind)
          | exact resolve b6e130 b6e51133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51133
        have b6e51676 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ x) X0) ∨ x = (M.op x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e130 x X0
             have i₂ := b6e51087 (σ X0)
             grind)
          | exact superpose b6e51087 b6e130
          | (have j1 := b6e51087 (σ X0)
             grind)
          | exact resolve b6e130 b6e51087
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51087
        have b6e69250 : ∀ X0 : G, (k (τ y) (τ X0)) = (τ (M.op x X0)) ∨ y = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e51232 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e51232
          | exact resolve b6e51232 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e69286 : (τ (M.op x (σ x))) = (k (τ y) y) ∨ y = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e51232 y
             have i₂ := b6e44 x
             grind)
          | exact superpose b6e44 b6e51232
          | (have j0 := b6e51232 x
             grind)
          | exact resolve b6e51232 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e69310 : ∀ X0 : G, (k (τ y) X0) = (M.op (k (τ y) X0) (k (τ y) X0)) ∨ y = (M.op x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e15172 x (σ X0)
             have i₂ := b6e51232 X0
             grind)
          | exact superpose b6e51232 b6e15172
          | (have j1 := b6e51232 X0
             grind)
          | exact resolve b6e15172 b6e51232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e69376 : ∀ X0 : G, (τ (M.op x X0)) = (τ (k y X0)) ∨ y = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e69250 X0
             have i₂ := b6e639 X0 y
             grind)
          | exact superpose b6e639 b6e69250
          | (have j0 := b6e69250 X0
             grind)
          | exact resolve b6e69250 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69250
        have b6e73485 : ∀ X0 X1 : G, (τ (k X1 (k y X0))) = (k (τ X1) (τ (M.op x X0))) ∨ y = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e639 (k y X0) X1
             have i₂ := b6e69376 X0
             grind)
          | exact superpose b6e69376 b6e639
          | (have j1 := b6e69376 X0
             grind)
          | exact resolve b6e639 b6e69376
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73486 : ∀ X0 X1 : G, (τ (k (k y X0) X1)) = (k (τ (M.op x X0)) (τ X1)) ∨ y = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e639 X1 (k y X0)
             have i₂ := b6e69376 X0
             grind)
          | exact superpose b6e69376 b6e639
          | (have j1 := b6e69376 X0
             grind)
          | exact resolve b6e639 b6e69376
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69376
        have b6e73540 : ∀ X0 X1 : G, (τ (k (k y X0) X1)) = (τ (k (M.op x X0) X1)) ∨ y = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e73486 X0 X1
             have i₂ := b6e639 X1 (M.op x X0)
             grind)
          | exact superpose b6e639 b6e73486
          | (have j0 := b6e73486 X0 X1
             grind)
          | exact resolve b6e73486 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73486
        have b6e73541 : ∀ X0 X1 : G, (τ (k X1 (k y X0))) = (τ (k X1 (M.op x X0))) ∨ y = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e73485 X0 X1
             have i₂ := b6e639 (M.op x X0) X1
             grind)
          | exact superpose b6e639 b6e73485
          | (have j0 := b6e73485 X0 X1
             grind)
          | exact resolve b6e73485 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73485
        have b6e79990 : ∀ X0 : G, (k y (σ X0)) = (σ (M.op (τ y) X0)) ∨ (τ y) = (M.op (τ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e28 y X0
             have i₂ := b6e16411 X0
             grind)
          | exact superpose b6e16411 b6e28
          | (have j1 := b6e16411 X0
             grind)
          | exact resolve b6e28 b6e16411
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16411
        have b6e84030 : ∀ X0 : G, (k (τ x) (τ X0)) = (τ (M.op x X0)) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e51676 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e51676
          | exact resolve b6e51676 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e84074 : (τ (M.op x (σ x))) = (k (τ x) y) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e51676 y
             have i₂ := b6e44 x
             grind)
          | exact superpose b6e44 b6e51676
          | (have j0 := b6e51676 x
             grind)
          | exact resolve b6e51676 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e84095 : (k (τ x) x) = (k y (k (τ x) x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e3973 x
             have i₂ := b6e51676 x
             grind)
          | exact superpose b6e51676 b6e3973
          | (have j1 := b6e51676 x
             grind)
          | exact resolve b6e3973 b6e51676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51676
        have b6e84179 : ∀ X0 : G, (τ (M.op x X0)) = (τ (k x X0)) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e84030 X0
             have i₂ := b6e639 X0 x
             grind)
          | exact superpose b6e639 b6e84030
          | (have j0 := b6e84030 X0
             grind)
          | exact resolve b6e84030 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84030
        have b6e87738 : ∀ X0 X1 : G, (k (τ X1) (τ (M.op x X0))) = (τ (k X1 (k x X0))) ∨ x = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e639 (k x X0) X1
             have i₂ := b6e84179 X0
             grind)
          | exact superpose b6e84179 b6e639
          | (have j1 := b6e84179 X0
             grind)
          | exact resolve b6e639 b6e84179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84179
        have b6e87800 : ∀ X0 X1 : G, (τ (k X1 (M.op x X0))) = (τ (k X1 (k x X0))) ∨ x = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e87738 X0 X1
             have i₂ := b6e639 (M.op x X0) X1
             grind)
          | exact superpose b6e639 b6e87738
          | (have j0 := b6e87738 X0 X1
             grind)
          | exact resolve b6e87738 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87738
        have b6e108870 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e39857 X0 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e39857
          | exact resolve b6e39857 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39857
        have b6e141950 : ∀ X0 : G, (τ X0) = (k (τ x) (τ X0)) ∨ (k (σ (τ x)) X0) = (σ (M.op (τ x) (τ X0))) ∨ (τ x) = (M.op (τ x) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e2145 X0 (τ x) (τ x)
             have i₂ := b6e15170
             grind)
          | exact superpose b6e15170 b6e2145
          | (have j0 := b6e2145 X0 (τ x) x
             grind)
          | exact resolve b6e2145 b6e15170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15170
        have b6e141951 : ∀ X0 : G, (τ X0) = (k (τ y) (τ X0)) ∨ (k (σ (τ y)) X0) = (σ (M.op (τ y) (τ X0))) ∨ (τ y) = (M.op (τ y) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e2145 X0 (τ y) (τ y)
             have i₂ := b6e15169
             grind)
          | exact superpose b6e15169 b6e2145
          | (have j0 := b6e2145 X0 (τ y) x
             grind)
          | exact resolve b6e2145 b6e15169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2145 b6e15169
        have b6e142177 : ∀ X0 : G, (τ X0) = (k (τ y) (τ X0)) ∨ (k (σ (τ y)) X0) = (σ (M.op (τ y) (τ X0))) := by
          intro X0
          first
          | (have j0 := b6e141951 X0
             have j1 := b6e15 (τ y) (τ X0)
             grind)
          | (have r₁ := b6e141951 X0
             have r₂ := b6e15 (τ y) (τ X0)
             grind)
          | exact resolve b6e141951 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141951
        have b6e142178 : ∀ X0 : G, (τ X0) = (k (τ x) (τ X0)) ∨ (k (σ (τ x)) X0) = (σ (M.op (τ x) (τ X0))) := by
          intro X0
          first
          | (have j0 := b6e141950 X0
             have j1 := b6e15 (τ x) (τ X0)
             grind)
          | (have r₁ := b6e141950 X0
             have r₂ := b6e15 (τ x) (τ X0)
             grind)
          | exact resolve b6e141950 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141950
        have b6e142268 : ∀ X0 : G, (τ X0) = (τ (k y X0)) ∨ (k (σ (τ y)) X0) = (σ (M.op (τ y) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e142177 X0
             have i₂ := b6e639 X0 y
             grind)
          | exact superpose b6e639 b6e142177
          | (have j0 := b6e142177 X0
             grind)
          | exact resolve b6e142177 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142177
        have b6e142269 : ∀ X0 : G, (τ X0) = (τ (k x X0)) ∨ (k (σ (τ x)) X0) = (σ (M.op (τ x) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e142178 X0
             have i₂ := b6e639 X0 x
             grind)
          | exact superpose b6e639 b6e142178
          | (have j0 := b6e142178 X0
             grind)
          | exact resolve b6e142178 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142178
        have b6e142330 : ∀ X0 : G, (k y X0) = (σ (M.op (τ y) (τ X0))) ∨ (τ X0) = (τ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b6e142268 X0
             have i₂ := b6e14 y
             grind)
          | exact superpose b6e14 b6e142268
          | (have j0 := b6e142268 X0
             grind)
          | exact resolve b6e142268 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142268
        have b6e142331 : ∀ X0 : G, (k x X0) = (σ (M.op (τ x) (τ X0))) ∨ (τ X0) = (τ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e142269 X0
             have i₂ := b6e14 x
             grind)
          | exact superpose b6e14 b6e142269
          | (have j0 := b6e142269 X0
             grind)
          | exact resolve b6e142269 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142269
        have b6e144050 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15172 (σ X0) (σ (M.op X0 X0))
             have i₂ := b6e2879 X0
             grind)
          | exact superpose b6e2879 b6e15172
          | (have j1 := b6e2879 X0
             grind)
          | exact resolve b6e15172 b6e2879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2879
        have b6e144089 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e144050 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e144050
          | (have j0 := b6e144050 X0
             grind)
          | exact resolve b6e144050 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144050
        have b6e144090 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e144089 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144089
        have b6e144584 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e41 (σ X0) X1 (σ X0)
             have i₂ := b6e144090 X0
             grind)
          | exact superpose b6e144090 b6e41
          | (have j1 := b6e144090 X0
             grind)
          | exact resolve b6e41 b6e144090
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e144585 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e42 (σ X0) (σ X0) X1
             have i₂ := b6e144090 X0
             grind)
          | exact superpose b6e144090 b6e42
          | (have j1 := b6e144090 X0
             grind)
          | exact resolve b6e42 b6e144090
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144090
        have b6e145628 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e144584 (τ X0) X1
             have i₂ := b6e127 X0 (τ X0)
             grind)
          | exact superpose b6e127 b6e144584
          | (have j0 := b6e144584 (τ X0) X1
             have j1 := b6e127 X0 (τ X0)
             grind)
          | exact resolve b6e144584 b6e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e127 b6e144584
        have b6e146006 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e145628 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e145628
        have b6e146068 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e146006 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e146006
          | (have j0 := b6e146006 X0 X1
             grind)
          | exact resolve b6e146006 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146006
        have b6e147206 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1346 X0 X0
             have i₂ := b6e144585 X0 (σ (M.op X0 X0))
             grind)
          | exact superpose b6e144585 b6e1346
          | (have j1 := b6e144585 X0 x
             grind)
          | exact resolve b6e1346 b6e144585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144585
        have b6e161618 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op (M.op X3 X1) (M.op X0 X2)) = (k (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X3 X1) = (M.op (M.op X3 X1) (M.op X0 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e108870 (M.op X3 X1) (M.op X0 X2)
             have i₂ := b6e12 X0 X1 X2 X3
             grind)
          | exact superpose b6e12 b6e108870
          | (have j0 := b6e108870 (M.op X3 X1) (M.op X0 X2)
             grind)
          | (have r₁ := b6e108870 (M.op X0 X1) (M.op X0 X2)
             have r₂ := b6e12 X0 X1 X2 X0
             grind)
          | exact resolve b6e108870 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108870
        have b6e161708 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (k (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (M.op (M.op X3 X1) (M.op X0 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e161618 X0 X1 X2 X3
             have i₂ := b6e12 X3 X2 X1 X0
             grind)
          | exact superpose b6e12 b6e161618
          | (have j0 := b6e161618 X0 X1 X2 X3
             grind)
          | exact resolve b6e161618 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e161618
        have b6e161714 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op X3 X2) ∨ (M.op X3 X2) = (k (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X3 X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e161708 X0 X1 X2 X3
             have i₂ := b6e12 X3 X2 X1 X0
             grind)
          | exact superpose b6e12 b6e161708
          | (have j0 := b6e161708 X0 X1 X2 X3
             grind)
          | exact resolve b6e161708 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e161708
        have b6e161717 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (k (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X3 X1) = (M.op X3 X2) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b6e161714 X0 X1 X2 X3
             have j1 := b6e2014 X0 X1 X3 X1 X2
             grind)
          | (have r₁ := b6e161714 X0 X1 X2 X2
             have r₂ := b6e2014 X0 X1 X2 X3 x
             grind)
          | (have r₁ := b6e161714 X2 X1 X2 X0
             have r₂ := b6e2014 X0 X1 X2 X3 x
             grind)
          | (have r₁ := b6e161714 X2 x X2 X2
             have r₂ := b6e2014 X0 X1 X2 x x
             grind)
          | exact resolve b6e161714 b6e2014
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2014 b6e161714
        have b6e199504 : ∀ X0 : G, (k x (σ X0)) = (σ (M.op (τ x) X0)) ∨ (τ (k x (σ X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e142331 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e142331
          | exact resolve b6e142331 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e199532 : ∀ X0 : G, (M.op (τ x) (τ X0)) = (τ (k x X0)) ∨ (τ X0) = (τ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e13 (M.op (τ x) (τ X0))
             have i₂ := b6e142331 X0
             grind)
          | exact superpose b6e142331 b6e13
          | (have j1 := b6e142331 X0
             grind)
          | exact resolve b6e13 b6e142331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142331
        have b6e199565 : ∀ X0 : G, (k x (σ X0)) = (σ (M.op (τ x) X0)) ∨ (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e199504 X0
             have i₂ := b6e130 x X0
             grind)
          | exact superpose b6e130 b6e199504
          | (have j0 := b6e199504 X0
             grind)
          | exact resolve b6e199504 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e199504
        have b6e200026 : ∀ X0 : G, (k x (σ X0)) = (M.op (k x (σ X0)) (k x (σ X0))) ∨ (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1346 (τ x) X0
             have i₂ := b6e199565 X0
             grind)
          | exact superpose b6e199565 b6e1346
          | (have j1 := b6e199565 X0
             grind)
          | exact resolve b6e1346 b6e199565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e199565
        have b6e203301 : ∀ X0 : G, (k y (σ X0)) = (σ (M.op (τ y) X0)) ∨ (τ (k y (σ X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e142330 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e142330
          | exact resolve b6e142330 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e203329 : ∀ X0 : G, (M.op (τ y) (τ X0)) = (τ (k y X0)) ∨ (τ X0) = (τ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b6e13 (M.op (τ y) (τ X0))
             have i₂ := b6e142330 X0
             grind)
          | exact superpose b6e142330 b6e13
          | (have j1 := b6e142330 X0
             grind)
          | exact resolve b6e13 b6e142330
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142330
        have b6e203363 : ∀ X0 : G, (k y (σ X0)) = (σ (M.op (τ y) X0)) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e203301 X0
             have i₂ := b6e130 y X0
             grind)
          | exact superpose b6e130 b6e203301
          | (have j0 := b6e203301 X0
             grind)
          | exact resolve b6e203301 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e203301
        have b6e203713 : ∀ X0 : G, (τ (k y (σ X0))) = (M.op (τ y) X0) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e13 (M.op (τ y) X0)
             have i₂ := b6e203363 X0
             grind)
          | exact superpose b6e203363 b6e13
          | (have j1 := b6e203363 X0
             grind)
          | exact resolve b6e13 b6e203363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e203363
        have b6e203741 : ∀ X0 : G, (k (τ y) X0) = (M.op (τ y) X0) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e203713 X0
             have i₂ := b6e130 y X0
             grind)
          | exact superpose b6e130 b6e203713
          | (have j0 := b6e203713 X0
             grind)
          | exact resolve b6e203713 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e203713
        have b6e204687 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (k x X0))) ∨ (τ X0) = (τ (k x X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e41 (τ X0) X1 (τ x)
             have i₂ := b6e199532 X0
             grind)
          | exact superpose b6e199532 b6e41
          | (have j1 := b6e199532 X0
             grind)
          | exact resolve b6e41 b6e199532
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e199532
        have b6e209760 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (k y X0))) ∨ (τ X0) = (τ (k y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e41 (τ X0) X1 (τ y)
             have i₂ := b6e203329 X0
             grind)
          | exact superpose b6e203329 b6e41
          | (have j1 := b6e203329 X0
             grind)
          | exact resolve b6e41 b6e203329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e203329
        have b6e215666 : ∀ X0 : G, (σ (τ (k X0 X0))) = (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e147206 (τ X0)
             have i₂ := b6e8724 X0
             grind)
          | exact superpose b6e8724 b6e147206
          | (have j0 := b6e147206 (τ X0)
             have j1 := b6e8724 X0
             grind)
          | exact resolve b6e147206 b6e8724
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8724 b6e147206
        have b6e215704 : ∀ X0 : G, (σ (τ (k X0 X0))) = (M.op (σ (τ X0)) (σ (τ (k X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have j0 := b6e215666 X0
             have j1 := b6e2329 X0
             grind)
          | (have r₁ := b6e215666 X0
             have r₂ := b6e2329 X0
             grind)
          | exact resolve b6e215666 b6e2329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2329 b6e215666
        have b6e215736 : ∀ X0 : G, (k X0 X0) = (M.op (σ (τ X0)) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e215704 X0
             have i₂ := b6e14 (k X0 X0)
             grind)
          | exact superpose b6e14 b6e215704
          | (have j0 := b6e215704 X0
             grind)
          | exact resolve b6e215704 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e215704
        have b6e215757 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e215736 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e215736
          | (have j0 := b6e215736 X0
             grind)
          | exact resolve b6e215736 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e215736
        have b6e215808 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e146068 X0 X0
             have i₂ := b6e215757 X0
             grind)
          | exact superpose b6e215757 b6e146068
          | (have j0 := b6e146068 X0 x
             have j1 := b6e215757 X0
             grind)
          | exact resolve b6e146068 b6e215757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146068 b6e215757
        have b6e215899 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e215808 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e215808
        have b6e217147 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (k (σ (τ X0)) (M.op X1 (σ (τ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e6189 (τ X0) (τ X0) x
             have i₂ := b6e215899 X0
             grind)
          | exact superpose b6e215899 b6e6189
          | (have j1 := b6e215899 X0
             grind)
          | exact resolve b6e6189 b6e215899
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6189 b6e215899
        have b6e217166 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e217147 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e217147
          | (have j0 := b6e217147 X0 X1
             grind)
          | exact resolve b6e217147 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e217147
        have b6e219730 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e217166 X1 X1
             have i₂ := b6e2198 X0 X1
             grind)
          | (have i₁ := b6e217166 X0 X1
             have i₂ := b6e2198 (M.op X1 X0) X1
             grind)
          | exact superpose b6e2198 b6e217166
          | (have j1 := b6e2198 X0 X1
             grind)
          | exact resolve b6e217166 b6e2198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2198 b6e217166
        have b6e219935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 ∨ (k X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e219730 X0 X1
             have j1 := b6e15 X1 X0
             grind)
          | (have r₁ := b6e219730 (M.op (k X1 X1) X1) X1
             have r₂ := b6e15 (k X1 X1) X1
             grind)
          | (have r₁ := b6e219730 X1 X0
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e219730 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e219730
        have b6e241285 : ∀ X0 X1 : G, (M.op x X0) = (k x (M.op X1 X0)) ∨ x = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e161717 X0 x x x
             have i₂ := b6e420
             grind)
          | exact superpose b6e420 b6e161717
          | exact resolve b6e161717 b6e420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e161717
        have b6e285473 : ∀ X0 X1 : G, (k (k y X0) X1) = (σ (τ (k (M.op x X0) X1))) ∨ y = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e14 (k (k y X0) X1)
             have i₂ := b6e73540 X0 X1
             grind)
          | exact superpose b6e73540 b6e14
          | (have j1 := b6e73540 X0 X1
             grind)
          | exact resolve b6e14 b6e73540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73540
        have b6e285489 : ∀ X0 X1 : G, (k (M.op x X0) X1) = (k (k y X0) X1) ∨ y = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e285473 X0 X1
             have i₂ := b6e14 (k (M.op x X0) X1)
             grind)
          | exact superpose b6e14 b6e285473
          | (have j0 := b6e285473 X0 X1
             grind)
          | exact resolve b6e285473 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e285473
        have b6e286752 : ∀ X0 X1 : G, (k X0 (k y X1)) = (σ (τ (k X0 (M.op x X1)))) ∨ y = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e14 (k X0 (k y X1))
             have i₂ := b6e73541 X1 X0
             grind)
          | exact superpose b6e73541 b6e14
          | (have j1 := b6e73541 X1 X1
             grind)
          | exact resolve b6e14 b6e73541
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73541
        have b6e286764 : ∀ X0 X1 : G, (k X0 (M.op x X1)) = (k X0 (k y X1)) ∨ y = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e286752 X0 X1
             have i₂ := b6e14 (k X0 (M.op x X1))
             grind)
          | exact superpose b6e14 b6e286752
          | (have j0 := b6e286752 X0 X1
             grind)
          | exact resolve b6e286752 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e286752
        have b6e287001 : ∀ X0 X1 : G, (k y X1) = (k (M.op X0 (k y X1)) (M.op x X1)) ∨ y = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e872 X0 (k y X1)
             have i₂ := b6e286764 (M.op X0 (k y X1)) X1
             grind)
          | exact superpose b6e286764 b6e872
          | (have j1 := b6e286764 X0 X1
             grind)
          | exact resolve b6e872 b6e286764
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e872
        have b6e287012 : ∀ X0 X1 : G, (k y X1) = (k (σ (M.op X0 (τ (k y X1)))) (M.op x X1)) ∨ y = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e912 (k y X1) X0
             have i₂ := b6e286764 (σ (M.op X0 (τ (k y X1)))) X1
             grind)
          | exact superpose b6e286764 b6e912
          | (have j1 := b6e286764 X0 X1
             grind)
          | exact resolve b6e912 b6e286764
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e286764
        have b6e300380 : ∀ X0 X1 : G, (M.op X1 (τ (σ X0))) = (M.op X1 (k (τ x) X0)) ∨ (τ (σ X0)) = (k (τ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e204687 (σ X1) X1
             have i₂ := b6e130 x X1
             grind)
          | exact superpose b6e130 b6e204687
          | exact resolve b6e204687 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204687
        have b6e300487 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (τ x) X0)) ∨ (τ (σ X0)) = (k (τ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e300380 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e300380
          | (have j0 := b6e300380 X0 X1
             grind)
          | exact resolve b6e300380 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e300380
        have b6e300492 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (τ x) X0)) ∨ (k (τ x) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e300487 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e300487
          | (have j0 := b6e300487 X0 X1
             grind)
          | exact resolve b6e300487 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e300487
        have b6e336483 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op x (σ X1)))) = (τ (σ (k X0 (k (τ x) X1)))) ∨ x = (M.op x (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e87800 (σ X1) (σ X0)
             have i₂ := b6e128 x X1 X0
             grind)
          | exact superpose b6e128 b6e87800
          | (have j0 := b6e87800 (σ X1) X1
             grind)
          | exact resolve b6e87800 b6e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128 b6e87800
        have b6e336620 : ∀ X0 X1 : G, (k X0 (k (τ x) X1)) = (τ (k (σ X0) (M.op x (σ X1)))) ∨ x = (M.op x (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e336483 X0 X1
             have i₂ := b6e13 (k X0 (k (τ x) X1))
             grind)
          | exact superpose b6e13 b6e336483
          | (have j0 := b6e336483 X0 X1
             grind)
          | exact resolve b6e336483 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e336483
        have b6e336629 : ∀ X0 X1 : G, (k X0 (k (τ x) X1)) = (k X0 (τ (M.op x (σ X1)))) ∨ x = (M.op x (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e336620 X0 X1
             have i₂ := b6e139 X0 (M.op x (σ X1))
             grind)
          | exact superpose b6e139 b6e336620
          | (have j0 := b6e336620 X0 X1
             grind)
          | exact resolve b6e336620 b6e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139 b6e336620
        have b6e356199 : ∀ X0 X1 : G, (M.op X1 (τ (σ X0))) = (M.op X1 (k (τ y) X0)) ∨ (τ (σ X0)) = (k (τ y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e209760 (σ X1) X1
             have i₂ := b6e130 y X1
             grind)
          | exact superpose b6e130 b6e209760
          | exact resolve b6e209760 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e209760
        have b6e356293 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (τ y) X0)) ∨ (τ (σ X0)) = (k (τ y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e356199 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e356199
          | (have j0 := b6e356199 X0 X1
             grind)
          | exact resolve b6e356199 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e356199
        have b6e356299 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (τ y) X0)) ∨ (k (τ y) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e356293 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e356293
          | (have j0 := b6e356293 X0 X1
             grind)
          | exact resolve b6e356293 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e356293
        have b6e356388 : ∀ X0 : G, (σ (M.op (τ y) X0)) = (k y (σ (k (τ y) X0))) ∨ (τ y) = (M.op (τ y) X0) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e79990 (k (τ y) X0)
             have i₂ := b6e356299 X0 (τ y)
             grind)
          | exact superpose b6e356299 b6e79990
          | (have j0 := b6e79990 X0
             have j1 := b6e356299 X0 x
             grind)
          | exact resolve b6e79990 b6e356299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79990 b6e356299
        have b6e356418 : ∀ X0 : G, (σ (M.op (τ y) X0)) = (k y (σ (k (τ y) X0))) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e356388 X0
             have j1 := b6e15 (τ y) X0
             grind)
          | (have r₁ := b6e356388 x
             have r₂ := b6e15 (τ y) x
             grind)
          | exact resolve b6e356388 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e356388
        have b6e356427 : ∀ X0 : G, (σ (M.op (τ y) X0)) = (k y (k y (σ X0))) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e356418 X0
             have i₂ := b6e28 y X0
             grind)
          | exact superpose b6e28 b6e356418
          | (have j0 := b6e356418 X0
             grind)
          | exact resolve b6e356418 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e356418
        have b6e427021 : ∀ X0 : G, (τ (σ (M.op (τ y) X0))) = (k (τ y) (k (τ y) X0)) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e642 y X0 y
             have i₂ := b6e356427 X0
             grind)
          | exact superpose b6e356427 b6e642
          | (have j1 := b6e356427 X0
             grind)
          | exact resolve b6e642 b6e356427
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e642 b6e356427
        have b6e427024 : ∀ X0 : G, (M.op (τ y) X0) = (k (τ y) (k (τ y) X0)) ∨ (k (τ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e427021 X0
             have i₂ := b6e13 (M.op (τ y) X0)
             grind)
          | exact superpose b6e13 b6e427021
          | (have j0 := b6e427021 X0
             grind)
          | exact resolve b6e427021 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e427021
        have b6e446501 : ∀ X0 : G, (M.op (τ y) (τ X0)) = (k (τ y) (τ (k y X0))) ∨ (τ X0) = (τ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b6e427024 (τ X0)
             have i₂ := b6e639 X0 y
             grind)
          | exact superpose b6e639 b6e427024
          | exact resolve b6e427024 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e427024
        have b6e446545 : ∀ X0 : G, (M.op (τ y) (τ X0)) = (τ (k y (k y X0))) ∨ (τ X0) = (τ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b6e446501 X0
             have i₂ := b6e639 (k y X0) y
             grind)
          | exact superpose b6e639 b6e446501
          | (have j0 := b6e446501 X0
             grind)
          | exact resolve b6e446501 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e446501
        have b6e691239 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 X1)
             have i₂ := b6e219935 X1 X0
             grind)
          | exact superpose b6e219935 b6e13
          | (have j1 := b6e219935 X1 X0
             grind)
          | exact resolve b6e13 b6e219935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e219935
        have b6e691287 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e691239 X0 X1
             have i₂ := b6e13 (M.op X0 X1)
             grind)
          | exact superpose b6e13 b6e691239
          | (have j0 := b6e691239 X0 X1
             grind)
          | exact resolve b6e691239 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e691239
        have b6e691543 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e691287 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e691287
        have b6e691746 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X2) (M.op X0 X2)) = X1 ∨ (k (M.op X0 X2) X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e691543 (M.op X0 X2) X1
             have i₂ := b6e42 X0 X2 X1
             grind)
          | exact superpose b6e42 b6e691543
          | (have j0 := b6e691543 (M.op X0 X2) X1
             grind)
          | exact resolve b6e691543 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e691543
        have b6e691770 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X2) = X1 ∨ (k (M.op X0 X2) X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e691746 X0 X1 X2
             have i₂ := b6e258 X0 X2 X0
             grind)
          | exact superpose b6e258 b6e691746
          | (have j0 := b6e691746 X0 X1 X2
             grind)
          | exact resolve b6e691746 b6e258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e258 b6e691746
        have b6e691856 : ∀ X0 : G, x ≠ x ∨ x = (M.op x X0) ∨ x = (k (M.op x X0) x) := by
          intro X0
          first
          | (have i₁ := b6e691770 x x X0
             have i₂ := b6e420
             grind)
          | exact superpose b6e420 b6e691770
          | (have j0 := b6e691770 x x X0
             grind)
          | (have r₁ := b6e691770 x x x
             have r₂ := b6e420
             grind)
          | exact resolve b6e691770 b6e420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e691770
        have b6e691858 : ∀ X0 : G, x = (M.op x X0) ∨ x = (k (M.op x X0) x) := by
          intro X0
          first
          | (have j0 := b6e691856 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e691856
        have b6e691864 : ∀ X0 : G, x = (k (M.op x X0) x) := by
          intro X0
          first
          | (have j0 := b6e691858 X0
             have j1 := b6e854 X0
             grind)
          | (have r₁ := b6e691858 X0
             have r₂ := b6e854 X0
             grind)
          | exact resolve b6e691858 b6e854
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e854 b6e691858
        have b6e779113 : ∀ X0 : G, (τ (k y X0)) = (M.op (τ (k y X0)) (τ (k y X0))) ∨ y = (M.op x (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e69310 (τ X0)
             have i₂ := b6e639 X0 y
             grind)
          | exact superpose b6e639 b6e69310
          | (have j0 := b6e69310 (τ X0)
             grind)
          | exact resolve b6e69310 b6e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e639 b6e69310
        have b6e779129 : ∀ X0 : G, (τ (k y X0)) = (M.op (τ (k y X0)) (τ (k y X0))) ∨ y = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e779113 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e779113
          | (have j0 := b6e779113 X0
             grind)
          | exact resolve b6e779113 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e779113
        have b6e779221 : ∀ X0 : G, (σ (τ (k y X0))) = (M.op (σ (τ (k y X0))) (σ (τ (k y X0)))) ∨ y = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e1346 (τ (k y X0)) (τ (k y X0))
             have i₂ := b6e779129 X0
             grind)
          | exact superpose b6e779129 b6e1346
          | (have j1 := b6e779129 X0
             grind)
          | exact resolve b6e1346 b6e779129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1346 b6e779129
        have b6e779229 : ∀ X0 : G, (k y X0) = (M.op (k y X0) (k y X0)) ∨ y = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e779221 X0
             have i₂ := b6e14 (k y X0)
             grind)
          | exact superpose b6e14 b6e779221
          | (have j0 := b6e779221 X0
             grind)
          | exact resolve b6e779221 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e779221
        have b6e779343 : ∀ X0 : G, (k y X0) = (k (k y X0) (M.op x X0)) ∨ y = (M.op x X0) ∨ y = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e287001 (k y X0) X0
             have i₂ := b6e779229 X0
             grind)
          | exact superpose b6e779229 b6e287001
          | (have j0 := b6e287001 X0 X0
             have j1 := b6e779229 X0
             grind)
          | exact resolve b6e287001 b6e779229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e287001 b6e779229
        have b6e779395 : ∀ X0 : G, (k y X0) = (k (k y X0) (M.op x X0)) ∨ y = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b6e779343 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e779343
        have b6e780012 : ∀ X0 X1 : G, (k y (M.op X1 X0)) = (k (k y (M.op X1 X0)) (M.op x X0)) ∨ y = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e779395 (M.op x X1)
             have i₂ := b6e41 X1 x x
             grind)
          | exact superpose b6e41 b6e779395
          | (have j0 := b6e779395 X0
             grind)
          | exact resolve b6e779395 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e779395
        have b6e799137 : ∀ X0 : G, (τ (k x (σ X0))) = (M.op (τ (k x (σ X0))) (τ (k x (σ X0)))) ∨ (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15172 (k x (σ X0)) (k x (σ X0))
             have i₂ := b6e200026 X0
             grind)
          | exact superpose b6e200026 b6e15172
          | (have j1 := b6e200026 X0
             grind)
          | exact resolve b6e15172 b6e200026
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15172 b6e200026
        have b6e799138 : ∀ X0 : G, (k (τ x) X0) = (M.op (k (τ x) X0) (k (τ x) X0)) ∨ (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e799137 x
             have i₂ := b6e130 x x
             grind)
          | exact superpose b6e130 b6e799137
          | (have j0 := b6e799137 X0
             grind)
          | exact resolve b6e799137 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e799137
        have b6e803839 : ∀ X0 : G, (k (τ x) X0) = (M.op (k (τ x) X0) X0) ∨ (k (τ x) X0) = X0 ∨ (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e300492 X0 (k (τ x) X0)
             have i₂ := b6e799138 X0
             grind)
          | exact superpose b6e799138 b6e300492
          | (have j0 := b6e300492 X0 x
             have j1 := b6e799138 X0
             grind)
          | exact resolve b6e300492 b6e799138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e300492 b6e799138
        have b6e803847 : ∀ X0 : G, (k (τ x) X0) = (M.op (k (τ x) X0) X0) ∨ (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e803839 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e803839
        have b6e806801 : (τ (M.op x (σ x))) = (k y (k (τ x) x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e3973 x
             have i₂ := b6e336629 y x
             grind)
          | exact superpose b6e336629 b6e3973
          | (have j1 := b6e336629 x x
             grind)
          | exact resolve b6e3973 b6e336629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e336629
        have b6e867591 : ∀ X0 : G, (k y (M.op X0 x)) = (k (k y (M.op X0 x)) x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b6e780012 x x
             have i₂ := b6e420
             grind)
          | exact superpose b6e420 b6e780012
          | exact resolve b6e780012 b6e420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e420 b6e780012
        have b6e867601 : ∀ X0 : G, (k y (M.op X0 x)) = (k (k y (M.op X0 x)) x) := by
          intro X0
          first
          | (have j0 := b6e867591 X0
             grind)
          | (have r₁ := b6e867591 X0
             have r₂ := b6e91
             grind)
          | exact resolve b6e867591 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e867591
        have b6e867690 : ∀ X0 : G, (k y (M.op X0 x)) = (k (M.op x (M.op X0 x)) x) ∨ y = (M.op x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e285489 (M.op X0 x) x
             have i₂ := b6e867601 X0
             grind)
          | exact superpose b6e867601 b6e285489
          | (have j0 := b6e285489 (M.op X0 x) x
             grind)
          | exact resolve b6e285489 b6e867601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e285489 b6e867601
        have b6e867691 : ∀ X0 : G, x = (k y (M.op X0 x)) ∨ y = (M.op x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e867690 X0
             have i₂ := b6e691864 (M.op X0 x)
             grind)
          | exact superpose b6e691864 b6e867690
          | (have j0 := b6e867690 X0
             grind)
          | exact resolve b6e867690 b6e691864
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e691864 b6e867690
        have b6e867716 : ∀ X0 : G, y = (M.op x x) ∨ x = (k y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e867691 X0
             have i₂ := b6e41 x x X0
             grind)
          | exact superpose b6e41 b6e867691
          | (have j0 := b6e867691 X0
             grind)
          | exact resolve b6e867691 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e867691
        have b6e867737 : ∀ X0 : G, x = (k y (M.op X0 x)) := by
          intro X0
          first
          | (have j0 := b6e867716 X0
             grind)
          | (have r₁ := b6e867716 X0
             have r₂ := b6e21
             grind)
          | exact resolve b6e867716 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e867716
        have b6e867833 : x = (k y (k (τ x) x)) ∨ x = (k (τ x) x) := by
          first
          | (have i₁ := b6e867737 (k (τ x) x)
             have i₂ := b6e803847 x
             grind)
          | exact superpose b6e803847 b6e867737
          | (have j1 := b6e803847 x
             grind)
          | exact resolve b6e867737 b6e803847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e869406 : x = (k (τ x) x) ∨ x = (M.op x (σ x)) ∨ x = (k (τ x) x) := by
          first
          | (have i₁ := b6e84095
             have i₂ := b6e867833
             grind)
          | exact superpose b6e867833 b6e84095
          | exact resolve b6e84095 b6e867833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84095 b6e867833
        have b6e869426 : x = (k (τ x) x) ∨ x = (M.op x (σ x)) := by grind
        clear b6e869406
        have b6e869467 : (τ (M.op x (σ x))) = (k y x) ∨ x = (M.op x (σ x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e806801
             have i₂ := b6e869426
             grind)
          | exact superpose b6e869426 b6e806801
          | exact resolve b6e806801 b6e869426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e806801 b6e869426
        have b6e869538 : (τ (M.op x (σ x))) = (k y x) ∨ x = (M.op x (σ x)) := by grind
        clear b6e869467
        have b6e869553 : x = (τ (M.op x (σ x))) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e869538
             have i₂ := b6e1380
             grind)
          | exact superpose b6e1380 b6e869538
          | exact resolve b6e869538 b6e1380
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e869538
        have b6e871371 : x = (k (τ x) y) ∨ x = (M.op x (σ x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e84074
             have i₂ := b6e869553
             grind)
          | exact superpose b6e869553 b6e84074
          | exact resolve b6e84074 b6e869553
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84074 b6e869553
        have b6e871475 : x = (k (τ x) y) ∨ x = (M.op x (σ x)) := by grind
        clear b6e871371
        have b6e871586 : x = (M.op x y) ∨ x = y ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e803847 y
             have i₂ := b6e871475
             grind)
          | exact superpose b6e871475 b6e803847
          | exact resolve b6e803847 b6e871475
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e803847 b6e871475
        have b6e871628 : x = y ∨ x = (M.op x (σ x)) := by
          first
          | (have r₁ := b6e871586
             have r₂ := b6e20
             grind)
          | exact resolve b6e871586 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e871586
        have b6e871648 : x = (M.op x (σ x)) := by
          first
          | (have r₁ := b6e871628
             have r₂ := b6e91
             grind)
          | exact resolve b6e871628 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e871628
        have b6e871658 : (τ x) = (k (τ y) y) ∨ x = y := by
          first
          | (have i₁ := b6e69286
             have i₂ := b6e871648
             grind)
          | exact superpose b6e871648 b6e69286
          | exact resolve b6e69286 b6e871648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69286
        have b6e871675 : (τ x) = (k (τ y) x) ∨ x = y := by
          first
          | (have i₁ := b6e51232 x
             have i₂ := b6e871648
             grind)
          | exact superpose b6e871648 b6e51232
          | exact resolve b6e51232 b6e871648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51232
        have b6e871708 : ∀ X0 : G, (k y (σ x)) = (k (σ (M.op X0 (τ (k y (σ x))))) x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b6e287012 X0 (σ x)
             have i₂ := b6e871648
             grind)
          | exact superpose b6e871648 b6e287012
          | exact resolve b6e287012 b6e871648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e287012
        have b6e871742 : (τ x) = (k x (τ x)) := by
          first
          | (have i₁ := b6e3129 x
             have i₂ := b6e871648
             grind)
          | exact superpose b6e871648 b6e3129
          | exact resolve b6e3129 b6e871648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3129
        have b6e871743 : (τ x) = (k y (τ x)) := by
          first
          | (have i₁ := b6e3973 x
             have i₂ := b6e871648
             grind)
          | exact superpose b6e871648 b6e3973
          | exact resolve b6e3973 b6e871648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3973 b6e871648
        have b6e872141 : ∀ X0 : G, (k y (σ x)) = (k (σ (M.op X0 (τ (k y (σ x))))) x) := by
          intro X0
          first
          | (have j0 := b6e871708 X0
             grind)
          | (have r₁ := b6e871708 X0
             have r₂ := b6e91
             grind)
          | exact resolve b6e871708 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e871708
        have b6e872154 : (τ x) = (k (τ y) x) := by
          first
          | (have r₁ := b6e871675
             have r₂ := b6e91
             grind)
          | exact resolve b6e871675 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e871675
        have b6e872161 : (τ x) = (k (τ y) y) := by
          first
          | (have r₁ := b6e871658
             have r₂ := b6e91
             grind)
          | exact resolve b6e871658 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e871658
        have b6e872215 : ∀ X0 : G, (k y (σ x)) = (k (σ (M.op X0 (k (τ y) x))) x) := by
          intro X0
          first
          | (have i₁ := b6e872141 X0
             have i₂ := b6e130 y x
             grind)
          | exact superpose b6e130 b6e872141
          | exact resolve b6e872141 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130 b6e872141
        have b6e872236 : ∀ X0 : G, (k y (σ x)) = (k (σ (M.op X0 (τ x))) x) := by
          intro X0
          first
          | (have i₁ := b6e872215 X0
             have i₂ := b6e872154
             grind)
          | exact superpose b6e872154 b6e872215
          | exact resolve b6e872215 b6e872154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e872154 b6e872215
        have b6e872246 : x = (k y (σ x)) := by
          first
          | (have i₁ := b6e872236 x
             have i₂ := b6e912 x x
             grind)
          | exact superpose b6e912 b6e872236
          | exact resolve b6e872236 b6e912
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e912 b6e872236
        have b6e873161 : (τ (k y x)) = (M.op (τ y) (τ (σ x))) ∨ (τ (σ x)) = (τ x) := by
          first
          | (have i₁ := b6e446545 (σ x)
             have i₂ := b6e872246
             grind)
          | exact superpose b6e872246 b6e446545
          | exact resolve b6e446545 b6e872246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e446545 b6e872246
        have b6e873535 : (M.op (τ y) x) = (τ (k y x)) ∨ (τ (σ x)) = (τ x) := by
          first
          | (have i₁ := b6e873161
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e873161
          | exact resolve b6e873161 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e873161
        have b6e873727 : (τ x) = (M.op (τ y) x) ∨ (τ (σ x)) = (τ x) := by
          first
          | (have i₁ := b6e873535
             have i₂ := b6e1380
             grind)
          | exact superpose b6e1380 b6e873535
          | exact resolve b6e873535 b6e1380
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1380 b6e873535
        have b6e873815 : (τ x) = (M.op (τ y) x) ∨ x = (τ x) := by
          first
          | (have i₁ := b6e873727
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e873727
          | exact resolve b6e873727 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e873727
        have b6e876043 : (τ x) = (M.op (τ y) y) ∨ y = (τ x) := by
          first
          | (have i₁ := b6e203741 y
             have i₂ := b6e872161
             grind)
          | exact superpose b6e872161 b6e203741
          | exact resolve b6e203741 b6e872161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e203741 b6e872161
        have b6e885087 : x = (k y (τ x)) ∨ x = (τ x) := by
          first
          | (have i₁ := b6e867737 (τ y)
             have i₂ := b6e873815
             grind)
          | exact superpose b6e873815 b6e867737
          | exact resolve b6e867737 b6e873815
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e867737 b6e873815
        have b6e885289 : x = (τ x) ∨ x = (τ x) := by
          first
          | (have i₁ := b6e885087
             have i₂ := b6e871743
             grind)
          | exact superpose b6e871743 b6e885087
          | exact resolve b6e885087 b6e871743
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e871743 b6e885087
        have b6e885290 : x = (τ x) := by grind
        clear b6e885289
        have b6e900642 : (M.op x y) = (k x (τ x)) ∨ x = (M.op x y) ∨ y = (τ x) := by
          first
          | (have i₁ := b6e241285 y (τ y)
             have i₂ := b6e876043
             grind)
          | exact superpose b6e876043 b6e241285
          | (have j0 := b6e241285 y x
             grind)
          | exact resolve b6e241285 b6e876043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e241285 b6e876043
        have b6e900788 : (M.op x y) = (k x (τ x)) ∨ y = (τ x) := by
          first
          | (have r₁ := b6e900642
             have r₂ := b6e20
             grind)
          | exact resolve b6e900642 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e900642
        have b6e900862 : (M.op x y) = (τ x) ∨ y = (τ x) := by
          first
          | (have i₁ := b6e900788
             have i₂ := b6e871742
             grind)
          | exact superpose b6e871742 b6e900788
          | exact resolve b6e900788 b6e871742
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e871742 b6e900788
        have b6e900915 : x = (M.op x y) ∨ y = (τ x) := by
          first
          | (have i₁ := b6e900862
             have i₂ := b6e885290
             grind)
          | exact superpose b6e885290 b6e900862
          | exact resolve b6e900862 b6e885290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e900862
        have b6e900942 : y = (τ x) := by
          first
          | (have r₁ := b6e900915
             have r₂ := b6e20
             grind)
          | exact resolve b6e900915 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e900915
        have b6e900953 : x = y := by
          first
          | (have i₁ := b6e900942
             have i₂ := b6e885290
             grind)
          | exact superpose b6e885290 b6e900942
          | exact resolve b6e900942 b6e885290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e885290 b6e900942
        have b6e900957 : False := by grind
        exact b6e900957
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
          have b7e48 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          have b7e51 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e52 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e51
            | exact resolve b7e51 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e55 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e52
               grind)
            | exact superpose b7e52 b7e14
            | exact resolve b7e14 b7e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e56 : x = (k x y) := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e55
            | exact resolve b7e55 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e90 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e91 : x = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b7e90
          have b7e93 : y = (M.op x x) := by
            first
            | (have r₁ := b7e91
               have r₂ := b7e21
               grind)
            | exact resolve b7e91 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e95 : False := by grind
          exact b7e95
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
          have b8e79 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b8e200 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e79 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e201 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e200
               have r₂ := b8e23
               grind)
            | exact resolve b8e200 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e200
          have b8e202 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e201
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e201
            | exact resolve b8e201 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e201
          have b8e203 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e202
               grind)
            | exact superpose b8e202 b8e20
            | exact resolve b8e20 b8e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e202
          have b8e380 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e203
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e203
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e203 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203
          have b8e381 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e380
          have b8e385 : x = (M.op x y) := by
            first
            | (have r₁ := b8e381
               have r₂ := b8e22
               grind)
            | exact resolve b8e381 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e381
          have b8e389 : False := by grind
          exact b8e389

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_x_x_pxy_Equation3744 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : x ≠ x ∨ x = (k x y) := by
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
        have b1e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k (τ X0) X1)
             have i₂ := b1e28 X0 X1
             grind)
          | exact superpose b1e28 b1e13
          | exact resolve b1e13 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 : G, (M.op x X0) = (M.op x (M.op X1 X0)) := by
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
        have b1e35 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op X1 X0)) := by
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
        have b1e36 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
        have b1e37 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) x) := by
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
        have b1e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
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
        have b1e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e15 (M.op X0 X2) (M.op X3 X1)
             have i₂ := b1e12 X0 X1 X2 X3
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 (M.op X0 X2) (M.op X3 X1)
             grind)
          | (have r₁ := b1e15 (M.op X0 X1) (M.op X3 X1)
             have r₂ := b1e12 X0 X1 X1 X3
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e39 x X1 X2 X3 x
             have i₂ := b1e12 X2 X1 x x
             grind)
          | exact superpose b1e12 b1e39
          | exact resolve b1e39 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e42 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b1e36 X0 x X2 X3 x
             have i₂ := b1e12 X0 X3 x x
             grind)
          | exact superpose b1e12 b1e36
          | exact resolve b1e36 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e43 : x = (M.op x x) := by
          first
          | (have i₁ := b1e34 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e34
          | exact resolve b1e34 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : x ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e16
          | (have j0 := b1e16 y x
             grind)
          | exact resolve b1e16 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (M.op (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X3 X1) = (k (M.op X3 X1) (M.op X0 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e16 (M.op X3 X1) (M.op X0 X2)
             have i₂ := b1e12 X0 X1 X2 X3
             grind)
          | exact superpose b1e12 b1e16
          | (have j0 := b1e16 (M.op X3 X1) (M.op X0 X2)
             grind)
          | (have r₁ := b1e16 (M.op X0 X1) (M.op X0 X2)
             have r₂ := b1e12 X0 X1 X2 X0
             grind)
          | exact resolve b1e16 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (k (M.op X3 X1) (M.op X0 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b1e54 X0 X1 X2 X3
             have j1 := b1e15 (M.op X3 X1) (M.op X0 X2)
             grind)
          | (have r₁ := b1e54 X0 X1 X2 X3
             have r₂ := b1e15 (M.op X3 X1) (M.op X0 X2)
             grind)
          | exact resolve b1e54 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e59 : x ≠ y ∨ y = (k y x) := by
          first
          | (have j1 := b1e15 y x
             grind)
          | (have r₁ := b1e51
             have r₂ := b1e15 y x
             grind)
          | exact resolve b1e51 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e64 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e43
             grind)
          | exact resolve b1e15 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e65 : x = (k x x) := by grind
        clear b1e64
        have b1e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e69 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e28 X0 X1
             have i₂ := b1e17 (τ X0) X1
             grind)
          | exact superpose b1e17 b1e28
          | (have j1 := b1e17 (τ X0) X1
             grind)
          | exact resolve b1e28 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e85 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op (M.op X1 X2) (M.op X0 y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 x X2 (M.op X0 x)
             have i₂ := b1e37 X0 x
             grind)
          | exact superpose b1e37 b1e12
          | exact resolve b1e12 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e89 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b1e85 x X1 x
             have i₂ := b1e12 X1 y x x
             grind)
          | exact superpose b1e12 b1e85
          | exact resolve b1e85 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85
        have b1e105 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (M.op (M.op X2 X1) X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 (M.op X2 X1) X0
             have i₂ := b1e41 X1 X0 X2
             grind)
          | exact superpose b1e41 b1e16
          | (have j0 := b1e16 (M.op X2 X1) X0
             grind)
          | (have r₁ := b1e16 (M.op X2 X1) X2
             have r₂ := b1e41 X1 X2 X2
             grind)
          | exact resolve b1e16 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e110 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e105 X0 X1 X2
             have j1 := b1e15 (M.op X2 X1) X0
             grind)
          | (have r₁ := b1e105 X1 X1 X2
             have r₂ := b1e15 (M.op X2 X1) X1
             grind)
          | exact resolve b1e105 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105
        have b1e134 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e42 (σ y) (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e42
          | exact resolve b1e42 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e144 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 (M.op X0 X2) X1
             have i₂ := b1e42 X0 X2 X1
             grind)
          | exact superpose b1e42 b1e15
          | (have j0 := b1e15 (M.op X0 X2) X1
             grind)
          | (have r₁ := b1e15 (M.op X0 x) x
             have r₂ := b1e42 X0 x x
             grind)
          | exact resolve b1e15 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e176 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e29 X1 X0
             have i₂ := b1e17 X0 (τ X1)
             grind)
          | exact superpose b1e17 b1e29
          | (have j1 := b1e17 X0 (τ X1)
             grind)
          | exact resolve b1e29 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e181 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e29 X1 X0
             grind)
          | exact superpose b1e29 b1e13
          | exact resolve b1e13 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e188 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e134 (σ x)
             grind)
          | exact superpose b1e134 b1e22
          | exact resolve b1e22 b1e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e282 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e33 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e33
          | exact resolve b1e33 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e332 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e40 X0 X1 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e398 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e56 X0 X1 X2 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e441 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e68 y x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e68
          | (have j0 := b1e68 y x
             grind)
          | exact resolve b1e68 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e465 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e41 (σ X1) X2 (σ X0)
             have i₂ := b1e68 X0 X1
             grind)
          | exact superpose b1e68 b1e41
          | (have j1 := b1e68 X0 X1
             grind)
          | exact resolve b1e41 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e466 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e42 (σ X0) (σ X1) X2
             have i₂ := b1e68 X0 X1
             grind)
          | exact superpose b1e68 b1e42
          | (have j1 := b1e68 X0 X1
             grind)
          | exact resolve b1e42 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e473 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (σ X0) (σ X1)
             have i₂ := b1e68 X0 X1
             grind)
          | exact superpose b1e68 b1e16
          | (have j0 := b1e16 (σ X0) (σ X1)
             have j1 := b1e68 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X0) (σ X1)
             have r₂ := b1e68 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X0) (σ X0)
             have r₂ := b1e68 X0 X0
             grind)
          | exact resolve b1e16 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e479 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op (σ X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e42 (σ X1) (σ X0) X2
             have i₂ := b1e68 X0 X1
             grind)
          | exact superpose b1e68 b1e42
          | (have j1 := b1e68 X0 X1
             grind)
          | exact resolve b1e42 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e482 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e68 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e483 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e68 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e484 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e482 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e482
        have b1e485 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e473 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e473
        have b1e486 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e485 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e485
        have b1e489 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e486 X0 X1
             have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b1e486 X0 X1
             have r₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e486 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e486
        have b1e503 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e489 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e489
          | (have j0 := b1e489 X0 X1
             grind)
          | exact resolve b1e489 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e489
        have b1e909 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e484 (M.op X0 X1)
             have i₂ := b1e398 X0 X1 X1
             grind)
          | exact superpose b1e398 b1e484
          | (have j0 := b1e484 (M.op X0 X1)
             grind)
          | exact resolve b1e484 b1e398
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e914 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e484 (τ X0)
             have i₂ := b1e29 X0 (τ X0)
             grind)
          | exact superpose b1e29 b1e484
          | (have j0 := b1e484 (τ X0)
             grind)
          | exact resolve b1e484 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e484
        have b1e916 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have j0 := b1e909 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e909
        have b1e919 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e914 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e914
          | (have j0 := b1e914 X0
             grind)
          | exact resolve b1e914 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e914
        have b1e922 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e919 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e919
          | (have j0 := b1e919 X0
             grind)
          | exact resolve b1e919 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e919
        have b1e930 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e922 (τ X0)
             have i₂ := b1e282 X0 X0
             grind)
          | exact superpose b1e282 b1e922
          | (have j0 := b1e922 (τ X0)
             grind)
          | exact resolve b1e922 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1072 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b1e110 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e110
        have b1e1162 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) := by
          intro X0 X1
          first
          | (have j0 := b1e144 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e144
        have b1e1199 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1162 (σ X1) (σ X0)
             have i₂ := b1e68 X0 X1
             grind)
          | exact superpose b1e68 b1e1162
          | (have j1 := b1e68 X0 X1
             grind)
          | exact resolve b1e1162 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1208 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e33 (M.op X0 (σ X1)) X1
             have i₂ := b1e1162 X0 (σ X1)
             grind)
          | exact superpose b1e1162 b1e33
          | exact resolve b1e33 b1e1162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1199 X0 X1
             have i₂ := b1e18 X0 X0
             grind)
          | exact superpose b1e18 b1e1199
          | (have j0 := b1e1199 X0 X1
             grind)
          | exact resolve b1e1199 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1199
        have b1e1219 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e503 (τ X0) X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e503
          | exact resolve b1e503 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1221 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e503 (k X1 (τ X0)) X1
             have i₂ := b1e29 X0 X1
             grind)
          | exact superpose b1e29 b1e503
          | exact resolve b1e503 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1224 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (σ (k X2 (k X0 (τ X1)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e503 X2 (k X0 (τ X1))
             have i₂ := b1e29 X1 X0
             grind)
          | exact superpose b1e29 b1e503
          | (have j0 := b1e503 X2 (k X0 (τ X1))
             grind)
          | exact resolve b1e503 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1231 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e503 y x
             grind)
          | exact superpose b1e503 b1e22
          | (have j1 := b1e503 y x
             grind)
          | exact resolve b1e22 b1e503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1233 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b1e134 (σ X0)
             have i₂ := b1e503 y X0
             grind)
          | exact superpose b1e503 b1e134
          | (have j1 := b1e503 y X0
             grind)
          | exact resolve b1e134 b1e503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1250 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e42 (σ X0) (σ X1) X2
             have i₂ := b1e503 X0 X1
             grind)
          | exact superpose b1e503 b1e42
          | (have j1 := b1e503 X0 X1
             grind)
          | exact resolve b1e42 b1e503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1261 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (k (σ (k X0 X1)) (M.op X2 (σ X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e332 (σ X0) (σ X1) X2
             have i₂ := b1e503 X0 X1
             grind)
          | exact superpose b1e503 b1e332
          | (have j1 := b1e503 X0 X1
             grind)
          | exact resolve b1e332 b1e503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e503
        have b1e1283 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1219 X0 X1
             have i₂ := b1e28 X0 X1
             grind)
          | exact superpose b1e28 b1e1219
          | (have j0 := b1e1219 X0 X1
             grind)
          | exact resolve b1e1219 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1219
        have b1e1286 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1283 X0 X1
             have i₂ := b1e28 X0 X1
             grind)
          | exact superpose b1e28 b1e1283
          | (have j0 := b1e1283 X0 X1
             grind)
          | exact resolve b1e1283 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1283
        have b1e1323 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e332 (σ x) (σ y) x
             have i₂ := b1e441
             grind)
          | exact superpose b1e441 b1e332
          | exact resolve b1e332 b1e441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e332
        have b1e1352 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e176 X0 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e176
          | exact resolve b1e176 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e176
        have b1e1384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e1352 X0 X1
             have i₂ := b1e18 X1 X0
             grind)
          | exact superpose b1e18 b1e1352
          | (have j0 := b1e1352 X0 X1
             grind)
          | exact resolve b1e1352 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1352
        have b1e1405 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e483 (τ X0) (τ X1)
             have i₂ := b1e282 X1 X0
             grind)
          | exact superpose b1e282 b1e483
          | (have j0 := b1e483 (τ X0) (τ X1)
             grind)
          | exact resolve b1e483 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1437 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e1405 X0 X1
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e1405
          | (have j0 := b1e1405 X0 X1
             grind)
          | exact resolve b1e1405 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1405
        have b1e1444 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e1437 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1437
          | (have j0 := b1e1437 X0 X1
             grind)
          | exact resolve b1e1437 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1437
        have b1e1447 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e1444 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1444
          | (have j0 := b1e1444 X0 X1
             grind)
          | exact resolve b1e1444 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1444
        have b1e1449 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e1447 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e1447
          | (have j0 := b1e1447 X0 X1
             grind)
          | exact resolve b1e1447 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1447
        have b1e1450 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1449 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e1449
          | (have j0 := b1e1449 X0 X1
             grind)
          | exact resolve b1e1449 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1449
        have b1e1451 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1450 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1450
          | (have j0 := b1e1450 X0 X1
             grind)
          | exact resolve b1e1450 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1450
        have b1e1479 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op X2 X1))) ∨ (τ X0) = (M.op (M.op X2 X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e69 X0 (M.op x X1)
             have i₂ := b1e41 X1 (τ X0) x
             grind)
          | exact superpose b1e41 b1e69
          | (have j0 := b1e69 X0 (M.op X2 X1)
             grind)
          | exact resolve b1e69 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e1511 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op X2 X1))) ∨ (τ X0) = (M.op X2 (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1479 X0 X1 X2
             have i₂ := b1e42 X2 X1 (τ X0)
             grind)
          | exact superpose b1e42 b1e1479
          | (have j0 := b1e1479 X0 X1 X2
             grind)
          | exact resolve b1e1479 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1479
        have b1e1552 : ∀ X0 X1 X2 : G, (M.op X2 (σ (σ X1))) = (M.op X2 (σ (σ (k X0 X1)))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e465 (σ X0) (σ X1) X2
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e465
          | (have j0 := b1e465 (σ X0) (σ X1) X2
             grind)
          | exact resolve b1e465 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1557 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e465 (τ X0) (τ X1) X2
             have i₂ := b1e282 X1 X0
             grind)
          | exact superpose b1e282 b1e465
          | (have j0 := b1e465 (τ X0) (τ X1) X2
             grind)
          | exact resolve b1e465 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e465
        have b1e1627 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1557 X0 X1 X2
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e1557
          | (have j0 := b1e1557 X0 X1 X2
             grind)
          | exact resolve b1e1557 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1557
        have b1e1633 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1627 X0 X1 X2
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e1627
          | (have j0 := b1e1627 X0 X1 X2
             grind)
          | exact resolve b1e1627 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1627
        have b1e1636 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1633 X0 X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1633
          | (have j0 := b1e1633 X0 X1 X2
             grind)
          | exact resolve b1e1633 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1633
        have b1e1638 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1636 X0 X1 X2
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e1636
          | (have j0 := b1e1636 X0 X1 X2
             grind)
          | exact resolve b1e1636 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1636
        have b1e1639 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X2 X1) = (M.op X2 (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1638 X0 X1 X2
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e1638
          | (have j0 := b1e1638 X0 X1 X2
             grind)
          | exact resolve b1e1638 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1638
        have b1e1640 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1639 X0 X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1639
          | (have j0 := b1e1639 X0 X1 X2
             grind)
          | exact resolve b1e1639 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1639
        have b1e1675 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e466 (τ X0) (τ X1) X2
             have i₂ := b1e282 X1 X0
             grind)
          | exact superpose b1e282 b1e466
          | (have j0 := b1e466 (τ X0) (τ X1) X2
             grind)
          | exact resolve b1e466 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e466
        have b1e1746 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1675 X0 X1 X2
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e1675
          | (have j0 := b1e1675 X0 X1 X2
             grind)
          | exact resolve b1e1675 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1675
        have b1e1749 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1746 X0 X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1746
          | (have j0 := b1e1746 X0 X1 X2
             grind)
          | exact resolve b1e1746 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1746
        have b1e1751 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1749 X0 X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1749
          | (have j0 := b1e1749 X0 X1 X2
             grind)
          | exact resolve b1e1749 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1749
        have b1e1752 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1751 X0 X1 X2
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e1751
          | (have j0 := b1e1751 X0 X1 X2
             grind)
          | exact resolve b1e1751 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1751
        have b1e1753 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1752 X0 X1 X2
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e1752
          | (have j0 := b1e1752 X0 X1 X2
             grind)
          | exact resolve b1e1752 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1752
        have b1e1754 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1753 X0 X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1753
          | (have j0 := b1e1753 X0 X1 X2
             grind)
          | exact resolve b1e1753 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1753
        have b1e1824 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (σ X2) X1) ∨ (M.op X0 (σ X2)) = (σ (k (τ X0) X2)) ∨ (M.op X0 (σ X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e479 (τ X0) X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e479
          | exact resolve b1e479 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1832 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e479 X0 X2 (σ X1)
             have i₂ := b1e68 X0 X1
             grind)
          | exact superpose b1e68 b1e479
          | (have j0 := b1e479 X0 X2 X2
             have j1 := b1e68 X0 X2
             grind)
          | exact resolve b1e479 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e2008 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e479 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e479
        have b1e2054 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (M.op X0 X1) = (M.op (σ X2) X1) ∨ (M.op X0 (σ X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1824 X0 X1 X2
             have i₂ := b1e28 X0 X2
             grind)
          | exact superpose b1e28 b1e1824
          | (have j0 := b1e1824 X0 X1 X2
             grind)
          | exact resolve b1e1824 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1824
        have b1e2164 : ∀ X0 X1 : G, (τ (τ (M.op X0 (σ (σ X1))))) = (k (τ (τ (M.op X0 (σ (σ X1))))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e33 (τ (M.op X0 (σ (σ X1)))) X1
             have i₂ := b1e1208 X0 (σ X1)
             grind)
          | exact superpose b1e1208 b1e33
          | exact resolve b1e33 b1e1208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2858 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) := by
          first
          | (have i₁ := b1e916 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e916
          | exact resolve b1e916 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2895 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) (M.op (σ (M.op X0 X1)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e398 (σ (M.op X0 X1)) (σ (M.op X0 X1)) X2
             have i₂ := b1e916 X0 X1
             grind)
          | exact superpose b1e916 b1e398
          | exact resolve b1e398 b1e916
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4620 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by grind
        have b1e5110 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e1286 X0 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1286
          | exact resolve b1e1286 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5128 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e33 X0 X1
             have i₂ := b1e1286 X0 X1
             grind)
          | exact superpose b1e1286 b1e33
          | (have j1 := b1e1286 X0 X1
             grind)
          | exact resolve b1e33 b1e1286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e1286
        have b1e5210 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e29 X1 X0
             have i₂ := b1e5110 (τ X1) X0
             grind)
          | exact superpose b1e5110 b1e29
          | (have j1 := b1e5110 (τ X1) X0
             grind)
          | exact resolve b1e29 b1e5110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5231 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (k (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e181 X0 X1
             have i₂ := b1e5110 X1 (σ X0)
             grind)
          | exact superpose b1e5110 b1e181
          | (have j1 := b1e5110 X1 (σ X0)
             grind)
          | exact resolve b1e181 b1e5110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5110
        have b1e5562 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1233 y
             grind)
          | exact superpose b1e1233 b1e21
          | (have j1 := b1e1233 y
             grind)
          | exact resolve b1e21 b1e1233
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5825 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1250 (τ X1) (τ X0) X2
             have i₂ := b1e282 X0 X1
             grind)
          | exact superpose b1e282 b1e1250
          | exact resolve b1e1250 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1250
        have b1e5936 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5825 X0 X1 X2
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e5825
          | (have j0 := b1e5825 X0 X1 X2
             grind)
          | exact resolve b1e5825 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5825
        have b1e5938 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5936 X0 X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e5936
          | (have j0 := b1e5936 X0 X1 X2
             grind)
          | exact resolve b1e5936 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5936
        have b1e5939 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5938 X0 X1 X2
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e5938
          | (have j0 := b1e5938 X0 X1 X2
             grind)
          | exact resolve b1e5938 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5938
        have b1e5940 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5939 X0 X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e5939
          | (have j0 := b1e5939 X0 X1 X2
             grind)
          | exact resolve b1e5939 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5939
        have b1e5942 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e5562
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e5562
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e5562 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5562
        have b1e5943 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e5942
        have b1e5944 : (σ x) ≠ (σ (M.op y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e5943
             have i₂ := b1e89 y
             grind)
          | exact superpose b1e89 b1e5943
          | exact resolve b1e5943 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5943
        have b1e5946 : (σ y) = (σ (M.op y x)) ∨ (σ x) ≠ (σ (M.op y x)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e5944
             have i₂ := b1e89 y
             grind)
          | exact superpose b1e89 b1e5944
          | exact resolve b1e5944 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5944
        have b1e5948 : (σ x) ≠ (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e5946
             have i₂ := b1e89 y
             grind)
          | exact superpose b1e89 b1e5946
          | exact resolve b1e5946 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5946
        have b1e6145 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (k X0 X2) X3)) ∨ (k X0 X2) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e398 (k X0 X1) X2 X2
             have i₂ := b1e5940 X0 X1 X2
             grind)
          | exact superpose b1e5940 b1e398
          | (have j1 := b1e5940 (M.op X0 X1) (M.op (k X0 X2) X3) X2
             grind)
          | exact resolve b1e398 b1e5940
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e6259 : (σ y) = (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e1231
             have i₂ := b1e1384 x y
             grind)
          | exact superpose b1e1384 b1e1231
          | (have j1 := b1e1384 x y
             grind)
          | exact resolve b1e1231 b1e1384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1231 b1e1384
        have b1e6334 : (σ y) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b1e6259
             have r₂ := b1e5948
             grind)
          | exact resolve b1e6259 b1e5948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5948 b1e6259
        have b1e6351 : (σ y) = (σ (M.op y x)) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e6334
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e6334
          | exact resolve b1e6334 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6334
        have b1e7453 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e930 (M.op X0 X1)
             have i₂ := b1e398 X0 X1 X1
             grind)
          | exact superpose b1e398 b1e930
          | (have j0 := b1e930 (M.op X0 X1)
             grind)
          | exact resolve b1e930 b1e398
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e7457 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
          first
          | (have i₁ := b1e930 x
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e930
          | (have j0 := b1e930 x
             grind)
          | exact resolve b1e930 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e930
        have b1e7466 : (τ x) = (M.op (τ x) (τ x)) := by grind
        clear b1e7457
        have b1e7467 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have j0 := b1e7453 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7453
        have b1e9312 : (τ (τ x)) = (M.op (τ (τ x)) (τ (τ x))) := by
          first
          | (have i₁ := b1e7467 (τ x) (τ x)
             have i₂ := b1e7466
             grind)
          | exact superpose b1e7466 b1e7467
          | exact resolve b1e7467 b1e7466
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7466 b1e7467
        have b1e9645 : ∀ X0 : G, (τ (τ x)) = (k (τ (τ x)) (M.op (τ (τ x)) X0)) := by
          intro X0
          first
          | (have i₁ := b1e398 (τ (τ x)) (τ (τ x)) x
             have i₂ := b1e9312
             grind)
          | exact superpose b1e9312 b1e398
          | exact resolve b1e398 b1e9312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e398 b1e9312
        have b1e10340 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ (k X0 X1))) (M.op X2 (σ (τ X1)))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1261 (τ X1) (τ X0) X2
             have i₂ := b1e282 X0 X1
             grind)
          | exact superpose b1e282 b1e1261
          | exact resolve b1e1261 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1261
        have b1e10480 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ (k X0 X1))) (M.op X2 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e10340 X0 X1 X2
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e10340
          | (have j0 := b1e10340 X0 X1 X2
             grind)
          | exact resolve b1e10340 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10340
        have b1e10498 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (k X0 X1) (M.op X2 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e10480 X0 X1 X2
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e10480
          | (have j0 := b1e10480 X0 X1 X2
             grind)
          | exact resolve b1e10480 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10480
        have b1e10500 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) = (k (k X0 X1) (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e10498 X0 X1 X2
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e10498
          | (have j0 := b1e10498 X0 X1 X2
             grind)
          | exact resolve b1e10498 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10498
        have b1e10501 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (k X0 X1) (M.op X2 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e10500 X0 X1 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e10500
          | (have j0 := b1e10500 X0 X1 X2
             grind)
          | exact resolve b1e10500 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10500
        have b1e10720 : ∀ X0 : G, (σ (τ (τ x))) = (k (τ x) (σ (M.op (τ (τ x)) X0))) := by
          intro X0
          first
          | (have i₁ := b1e28 (τ x) (M.op (τ (τ x)) X0)
             have i₂ := b1e9645 X0
             grind)
          | exact superpose b1e9645 b1e28
          | exact resolve b1e28 b1e9645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9645
        have b1e10761 : ∀ X0 : G, (τ x) = (k (τ x) (σ (M.op (τ (τ x)) X0))) := by
          intro X0
          first
          | (have i₁ := b1e10720 X0
             have i₂ := b1e14 (τ x)
             grind)
          | exact superpose b1e14 b1e10720
          | exact resolve b1e10720 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10720
        have b1e10977 : ∀ X0 : G, (σ (τ x)) = (k x (σ (σ (M.op (τ (τ x)) X0)))) := by
          intro X0
          first
          | (have i₁ := b1e28 x (σ (M.op (τ (τ x)) X0))
             have i₂ := b1e10761 X0
             grind)
          | exact superpose b1e10761 b1e28
          | exact resolve b1e28 b1e10761
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10761
        have b1e11027 : ∀ X0 : G, x = (k x (σ (σ (M.op (τ (τ x)) X0)))) := by
          intro X0
          first
          | (have i₁ := b1e10977 X0
             have i₂ := b1e14 x
             grind)
          | exact superpose b1e14 b1e10977
          | exact resolve b1e10977 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10977
        have b1e11792 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1323 (σ x)
             have i₂ := b1e441
             grind)
          | exact superpose b1e441 b1e1323
          | exact resolve b1e1323 b1e441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e441 b1e1323
        have b1e11820 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
        clear b1e11792
        have b1e11838 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have r₁ := b1e11820
             have r₂ := b1e4620
             grind)
          | exact resolve b1e11820 b1e4620
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4620 b1e11820
        have b1e11856 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b1e11838
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e11838
          | exact resolve b1e11838 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11838
        have b1e11897 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e11856
             grind)
          | exact superpose b1e11856 b1e13
          | exact resolve b1e13 b1e11856
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11856
        have b1e12008 : (σ x) = (σ (k y x)) ∨ y = (k y y) := by
          first
          | (have i₁ := b1e11897
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e11897
          | exact resolve b1e11897 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11897
        have b1e12182 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (k y x) (τ X0)) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b1e181 (k y x) X0
             have i₂ := b1e12008
             grind)
          | exact superpose b1e12008 b1e181
          | exact resolve b1e181 b1e12008
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12008
        have b1e12229 : ∀ X0 : G, (k x (τ X0)) = (k (k y x) (τ X0)) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b1e12182 X0
             have i₂ := b1e181 x X0
             grind)
          | exact superpose b1e181 b1e12182
          | exact resolve b1e12182 b1e181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12182
        have b1e12692 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e2054 X0 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e2054
          | exact resolve b1e2054 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2054
        have b1e14457 : (M.op y x) = (τ (σ y)) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e6351
             grind)
          | exact superpose b1e6351 b1e13
          | exact resolve b1e13 b1e6351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6351
        have b1e14564 : y = (M.op y x) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e14457
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e14457
          | exact resolve b1e14457 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14457
        have b1e14565 : y = (M.op y x) ∨ x = y := by grind
        clear b1e14564
        have b1e15172 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b1e1072 y x
             have i₂ := b1e14565
             grind)
          | exact superpose b1e14565 b1e1072
          | exact resolve b1e1072 b1e14565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e15173 : y = (k y x) ∨ x = y := by
          first
          | (have i₁ := b1e1162 y x
             have i₂ := b1e14565
             grind)
          | exact superpose b1e14565 b1e1162
          | exact resolve b1e1162 b1e14565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e15180 : y = (k y x) := by
          first
          | (have r₁ := b1e15173
             have r₂ := b1e59
             grind)
          | exact resolve b1e15173 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e15173
        have b1e15621 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e483 y x
             have i₂ := b1e15180
             grind)
          | exact superpose b1e15180 b1e483
          | (have j0 := b1e483 y x
             grind)
          | exact resolve b1e483 b1e15180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e15628 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b1e15621
        have b1e15633 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e15628
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15628
          | exact resolve b1e15628 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15628
        have b1e15790 : ∀ X0 X1 X2 : G, (σ X0) ≠ (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (σ (k X0 (k X1 (τ X2)))) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e1224 X1 X2 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1224
        have b1e17321 : ∀ X0 X1 X2 : G, (τ (σ (M.op (τ (σ X0)) X1))) = (k X0 (τ (σ (M.op X2 X1)))) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e181 X0 (σ (M.op X2 X1))
             have i₂ := b1e1511 (σ X0) X1 X2
             grind)
          | exact superpose b1e1511 b1e181
          | (have j1 := b1e1511 (σ X0) X1 X2
             grind)
          | exact resolve b1e181 b1e1511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1511
        have b1e17374 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X1)) = (τ (σ (M.op (τ (σ X0)) X1))) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e17321 X0 X1 X2
             have i₂ := b1e13 (M.op X2 X1)
             grind)
          | exact superpose b1e13 b1e17321
          | (have j0 := b1e17321 X0 X1 X2
             grind)
          | exact resolve b1e17321 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17321
        have b1e17418 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X1)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e17374 X0 X1 X2
             have i₂ := b1e13 (M.op (τ (σ X0)) X1)
             grind)
          | exact superpose b1e13 b1e17374
          | (have j0 := b1e17374 X0 X1 X2
             grind)
          | exact resolve b1e17374 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17374
        have b1e17452 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e17418 X0 X1 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e17418
          | (have j0 := b1e17418 X0 X1 X2
             grind)
          | exact resolve b1e17418 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17418
        have b1e17472 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e17452 X0 X1 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e17452
          | (have j0 := b1e17452 X0 X1 X2
             grind)
          | exact resolve b1e17452 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17452
        have b1e17482 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e17472 X0 X1 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e17472
          | (have j0 := b1e17472 X0 X1 X2
             grind)
          | exact resolve b1e17472 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17472
        have b1e19063 : (σ y) = (σ (k y y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1233 y
             have i₂ := b1e15633
             grind)
          | exact superpose b1e15633 b1e1233
          | (have j0 := b1e1233 y
             grind)
          | exact resolve b1e1233 b1e15633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1233 b1e15633
        have b1e19144 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b1e19063
        have b1e19262 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k y y))) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 (k y y)
             have i₂ := b1e19144
             grind)
          | exact superpose b1e19144 b1e18
          | exact resolve b1e18 b1e19144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e19276 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (k y y) (τ X0)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e181 (k y y) X0
             have i₂ := b1e19144
             grind)
          | exact superpose b1e19144 b1e181
          | exact resolve b1e181 b1e19144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19144
        have b1e19382 : ∀ X0 : G, (k y (τ X0)) = (k (k y y) (τ X0)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e19276 X0
             have i₂ := b1e181 y X0
             grind)
          | exact superpose b1e181 b1e19276
          | exact resolve b1e19276 b1e181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19276
        have b1e19396 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (k y y))) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e19262 X0
             have i₂ := b1e18 X0 y
             grind)
          | exact superpose b1e18 b1e19262
          | exact resolve b1e19262 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19262
        have b1e20844 : ∀ X0 X1 X2 : G, (M.op (k (σ (τ (M.op X0 (σ (τ X1))))) X1) (σ X2)) = (σ (k (τ (M.op X0 (σ (τ X1)))) X2)) ∨ (k (σ (τ (M.op X0 (σ (τ X1))))) X1) = (σ (k (τ (M.op X0 (σ (τ X1)))) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1221 (τ (M.op X0 (σ (τ X1)))) X1 X2
             have i₂ := b1e1208 X0 (τ X1)
             grind)
          | exact superpose b1e1208 b1e1221
          | exact resolve b1e1221 b1e1208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1208 b1e1221
        have b1e21090 : ∀ X0 X1 X2 : G, (M.op (k (σ (τ (M.op X0 (σ (τ X1))))) X1) (σ X2)) = (k (M.op X0 (σ (τ X1))) (σ X2)) ∨ (k (σ (τ (M.op X0 (σ (τ X1))))) X1) = (σ (k (τ (M.op X0 (σ (τ X1)))) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e20844 X0 X1 X2
             have i₂ := b1e28 (M.op X0 (σ (τ X1))) X2
             grind)
          | exact superpose b1e28 b1e20844
          | (have j0 := b1e20844 X0 X1 X2
             grind)
          | exact resolve b1e20844 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e20844
        have b1e21170 : ∀ X0 X1 X2 : G, (M.op (k (σ (τ (M.op X0 X1))) X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (k (σ (τ (M.op X0 (σ (τ X1))))) X1) = (σ (k (τ (M.op X0 (σ (τ X1)))) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21090 X0 X0 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e21090
          | (have j0 := b1e21090 X0 X1 X2
             grind)
          | exact resolve b1e21090 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21090
        have b1e21232 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X1) X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (k (σ (τ (M.op X0 (σ (τ X1))))) X1) = (σ (k (τ (M.op X0 (σ (τ X1)))) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21170 X0 X1 X2
             have i₂ := b1e14 (M.op X0 X1)
             grind)
          | exact superpose b1e14 b1e21170
          | (have j0 := b1e21170 X0 X1 X2
             grind)
          | exact resolve b1e21170 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21170
        have b1e21260 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (k (σ (τ (M.op X0 (σ (τ X1))))) X1) = (σ (k (τ (M.op X0 (σ (τ X1)))) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21232 X0 X1 X2
             have i₂ := b1e1162 X0 X1
             grind)
          | exact superpose b1e1162 b1e21232
          | (have j0 := b1e21232 X0 X1 X2
             grind)
          | exact resolve b1e21232 b1e1162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21232
        have b1e21274 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (k (σ (τ (M.op X0 (σ (τ X1))))) X1) = (σ (k (τ (M.op X0 (σ (τ X1)))) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21260 X0 X1 X2
             have i₂ := b1e42 X0 X1 (σ X2)
             grind)
          | exact superpose b1e42 b1e21260
          | (have j0 := b1e21260 X0 X1 X2
             grind)
          | exact resolve b1e21260 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21260
        have b1e21276 : ∀ X0 X1 X2 : G, (k (σ (τ (M.op X0 (σ (τ X1))))) X1) = (k (M.op X0 (σ (τ X1))) (σ X2)) ∨ (M.op X0 (σ X2)) = (k (M.op X0 X1) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21274 X0 X1 X2
             have i₂ := b1e28 (M.op X0 (σ (τ X1))) X2
             grind)
          | exact superpose b1e28 b1e21274
          | (have j0 := b1e21274 X0 X1 X2
             grind)
          | exact resolve b1e21274 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21274
        have b1e21278 : ∀ X0 X1 X2 : G, (k (σ (τ (M.op X0 X1))) X1) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 (σ X2)) = (k (M.op X0 X1) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21276 X0 X0 X2
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e21276
          | (have j0 := b1e21276 X0 X1 X2
             grind)
          | exact resolve b1e21276 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21276
        have b1e21280 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X1) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 (σ X2)) = (k (M.op X0 X1) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21278 X0 X1 X2
             have i₂ := b1e14 (M.op X0 X1)
             grind)
          | exact superpose b1e14 b1e21278
          | (have j0 := b1e21278 X0 X1 X2
             grind)
          | exact resolve b1e21278 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21278
        have b1e21282 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 (σ X2)) = (k (M.op X0 X1) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21280 X0 X1 X2
             have i₂ := b1e1162 X0 X1
             grind)
          | exact superpose b1e1162 b1e21280
          | (have j0 := b1e21280 X0 X1 X2
             grind)
          | exact resolve b1e21280 b1e1162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1162 b1e21280
        have b1e30893 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e2008 (τ X1) (τ X0)
             have i₂ := b1e282 X0 X1
             grind)
          | exact superpose b1e282 b1e2008
          | (have j0 := b1e2008 (τ X0) (τ X1)
             grind)
          | exact resolve b1e2008 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2008
        have b1e31075 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e30893 X0 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e30893
          | (have j0 := b1e30893 X0 X1
             grind)
          | exact resolve b1e30893 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30893
        have b1e31126 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e31075 X0 X1
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e31075
          | (have j0 := b1e31075 X0 X1
             grind)
          | exact resolve b1e31075 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31075
        have b1e31159 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e31126 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e31126
          | (have j0 := b1e31126 X0 X1
             grind)
          | exact resolve b1e31126 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31126
        have b1e31177 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e31159 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e31159
          | (have j0 := b1e31159 X0 X1
             grind)
          | exact resolve b1e31159 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31159
        have b1e31188 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e31177 X0 X1
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e31177
          | (have j0 := b1e31177 X0 X1
             grind)
          | exact resolve b1e31177 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31177
        have b1e31195 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e31188 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e31188
          | (have j0 := b1e31188 X0 X1
             grind)
          | exact resolve b1e31188 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31188
        have b1e31198 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e31195 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e31195
          | (have j0 := b1e31195 X0 X1
             grind)
          | exact resolve b1e31195 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31195
        have b1e57897 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X1))) = (k (M.op X0 X1) (τ (M.op (σ (M.op X0 X1)) X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e181 (M.op X0 X1) (M.op (σ (M.op X0 X1)) X2)
             have i₂ := b1e2895 X0 X1 X2
             grind)
          | exact superpose b1e2895 b1e181
          | exact resolve b1e181 b1e2895
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2895
        have b1e57942 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (τ (M.op (σ (M.op X0 X1)) X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e57897 X0 X1 X2
             have i₂ := b1e13 (M.op X0 X1)
             grind)
          | exact superpose b1e13 b1e57897
          | exact resolve b1e57897 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57897
        have b1e58222 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) (τ (M.op (σ (σ (M.op X0 X1))) X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e57942 (σ (M.op X0 X1)) (σ (M.op X0 X1)) X2
             have i₂ := b1e916 X0 X1
             grind)
          | exact superpose b1e916 b1e57942
          | exact resolve b1e57942 b1e916
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57942
        have b1e62875 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e5128 X0 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e5128
          | exact resolve b1e5128 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5128
        have b1e63194 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e62875 X0 X1
             have i₂ := b1e282 X0 X1
             grind)
          | exact superpose b1e282 b1e62875
          | (have j0 := b1e62875 X0 X1
             grind)
          | exact resolve b1e62875 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62875
        have b1e63792 : ∀ X0 X1 X2 : G, (τ (k X2 (k X0 X1))) = (k (τ X2) (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e282 (k X0 X1) X2
             have i₂ := b1e63194 X1 X0
             grind)
          | exact superpose b1e63194 b1e282
          | (have j1 := b1e63194 X1 X0
             grind)
          | exact resolve b1e282 b1e63194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63793 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e282 X2 (k X0 X1)
             have i₂ := b1e63194 X1 X0
             grind)
          | exact superpose b1e63194 b1e282
          | (have j1 := b1e63194 X1 X0
             grind)
          | exact resolve b1e282 b1e63194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63194
        have b1e63886 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e63793 X0 X1 X2
             have i₂ := b1e282 X2 (M.op X0 X1)
             grind)
          | exact superpose b1e282 b1e63793
          | (have j0 := b1e63793 X0 X1 X2
             grind)
          | exact resolve b1e63793 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63793
        have b1e63887 : ∀ X0 X1 X2 : G, (τ (k X2 (k X0 X1))) = (τ (k X2 (M.op X0 X1))) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e63792 X0 X1 X2
             have i₂ := b1e282 (M.op X0 X1) X2
             grind)
          | exact superpose b1e282 b1e63792
          | (have j0 := b1e63792 X0 X1 X2
             grind)
          | exact resolve b1e63792 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63792
        have b1e74903 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e5210 X0 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e5210
          | exact resolve b1e5210 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74992 : ∀ X0 : G, x = (k x (σ (k (σ (τ (τ x))) X0))) ∨ (τ (τ x)) = (k (τ (τ x)) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e11027 (τ X0)
             have i₂ := b1e5210 (τ (τ x)) X0
             grind)
          | exact superpose b1e5210 b1e11027
          | (have j1 := b1e5210 (τ (τ x)) X0
             grind)
          | exact resolve b1e11027 b1e5210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5210 b1e11027
        have b1e75178 : ∀ X0 : G, x = (k x (σ (k (τ x) X0))) ∨ (τ (τ x)) = (k (τ (τ x)) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e74992 X0
             have i₂ := b1e14 (τ x)
             grind)
          | exact superpose b1e14 b1e74992
          | (have j0 := b1e74992 X0
             grind)
          | exact resolve b1e74992 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74992
        have b1e75197 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e74903 X0 X1
             have i₂ := b1e18 X1 X0
             grind)
          | exact superpose b1e18 b1e74903
          | (have j0 := b1e74903 X0 X1
             grind)
          | exact resolve b1e74903 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74903
        have b1e75201 : ∀ X0 : G, x = (k x (k x (σ X0))) ∨ (τ (τ x)) = (k (τ (τ x)) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e75178 X0
             have i₂ := b1e28 x X0
             grind)
          | exact superpose b1e28 b1e75178
          | (have j0 := b1e75178 X0
             grind)
          | exact resolve b1e75178 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75178
        have b1e75211 : ∀ X0 : G, x = (k x (k x (σ X0))) ∨ (τ (τ x)) = (τ (k (τ x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e75201 X0
             have i₂ := b1e282 X0 (τ x)
             grind)
          | exact superpose b1e282 b1e75201
          | (have j0 := b1e75201 X0
             grind)
          | exact resolve b1e75201 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75201
        have b1e83272 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
          intro X0 X1
          first
          | (have j0 := b1e1552 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1552
        have b1e83273 : ∀ X0 X1 : G, (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
          intro X0 X1
          first
          | (have j0 := b1e83272 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83272
        have b1e119034 : ∀ X0 : G, (k x X0) = (k (k y x) X0) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b1e12229 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e12229
          | exact resolve b1e12229 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12229
        have b1e119261 : ∀ X0 : G, (k y X0) = (k x X0) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b1e119034 X0
             have i₂ := b1e15180
             grind)
          | exact superpose b1e15180 b1e119034
          | exact resolve b1e119034 b1e15180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15180 b1e119034
        have b1e120353 : y ≠ (k x y) ∨ y = (M.op y y) ∨ y = (k y y) := by
          first
          | (have i₁ := b1e922 y
             have i₂ := b1e119261 y
             grind)
          | exact superpose b1e119261 b1e922
          | (have j0 := b1e922 y
             grind)
          | (have r₁ := b1e922 y
             have r₂ := b1e119261 x
             grind)
          | exact resolve b1e922 b1e119261
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e120530 : y ≠ (k x y) ∨ y = (k y y) := by grind
        clear b1e119261
        have b1e120565 : x ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e120530
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e120530
          | exact resolve b1e120530 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120530
        have b1e120674 : y ≠ (k x y) ∨ y = (M.op y y) := by
          first
          | (have j1 := b1e922 y
             grind)
          | (have r₁ := b1e120353
             have r₂ := b1e922 y
             grind)
          | exact resolve b1e120353 b1e922
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120353
        have b1e120682 : y = (k y y) := by
          first
          | (have r₁ := b1e120565
             have r₂ := b1e15172
             grind)
          | exact resolve b1e120565 b1e15172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15172 b1e120565
        have b1e120718 : x ≠ y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e120674
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e120674
          | exact resolve b1e120674 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e120674
        have b1e120722 : y = (M.op y x) ∨ x ≠ y := by
          first
          | (have i₁ := b1e120718
             have i₂ := b1e89 y
             grind)
          | exact superpose b1e89 b1e120718
          | exact resolve b1e120718 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120718
        have b1e120723 : y = (M.op y x) := by
          first
          | (have r₁ := b1e120722
             have r₂ := b1e14565
             grind)
          | exact resolve b1e120722 b1e14565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14565 b1e120722
        have b1e121791 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e483 y y
             have i₂ := b1e120682
             grind)
          | exact superpose b1e120682 b1e483
          | (have j0 := b1e483 y y
             grind)
          | exact resolve b1e483 b1e120682
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e483
        have b1e121833 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e121791
        have b1e121834 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e121833
        have b1e121852 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e121834
             have i₂ := b1e134 (σ y)
             grind)
          | exact superpose b1e134 b1e121834
          | exact resolve b1e121834 b1e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e134 b1e121834
        have b1e124647 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e121852
             grind)
          | exact superpose b1e121852 b1e21
          | exact resolve b1e21 b1e121852
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e219646 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e1832 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1832
        have b1e219656 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e219646 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e219646
        have b1e219657 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e219656 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e219656
        have b1e274948 : ∀ X0 : G, (k y y) ≠ (k y (τ X0)) ∨ (k y y) = (M.op (τ X0) (k y y)) ∨ (k y y) = (M.op (k y y) (τ X0)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e1451 (k y y) (τ X0)
             have i₂ := b1e19382 X0
             grind)
          | exact superpose b1e19382 b1e1451
          | (have j0 := b1e1451 (k y y) (τ X0)
             grind)
          | exact resolve b1e1451 b1e19382
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19382
        have b1e274989 : ∀ X0 : G, (k y y) ≠ (k y (τ X0)) ∨ (k y y) = (M.op (τ X0) (k y y)) ∨ (k y y) = (M.op (k y y) (τ X0)) := by
          intro X0
          first
          | (have j0 := b1e274948 X0
             grind)
          | (have r₁ := b1e274948 X0
             have r₂ := b1e124647
             grind)
          | exact resolve b1e274948 b1e124647
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e274948
        have b1e275040 : ∀ X0 : G, y ≠ (k y (τ X0)) ∨ (k y y) = (M.op (τ X0) (k y y)) ∨ (k y y) = (M.op (k y y) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e274989 X0
             have i₂ := b1e120682
             grind)
          | exact superpose b1e120682 b1e274989
          | (have j0 := b1e274989 X0
             grind)
          | exact resolve b1e274989 b1e120682
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e274989
        have b1e275076 : ∀ X0 : G, y = (M.op (τ X0) y) ∨ y ≠ (k y (τ X0)) ∨ (k y y) = (M.op (k y y) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e275040 X0
             have i₂ := b1e120682
             grind)
          | exact superpose b1e120682 b1e275040
          | (have j0 := b1e275040 X0
             grind)
          | exact resolve b1e275040 b1e120682
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e275040
        have b1e275091 : ∀ X0 : G, y = (M.op (τ X0) x) ∨ y ≠ (k y (τ X0)) ∨ (k y y) = (M.op (k y y) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e275076 X0
             have i₂ := b1e89 (τ X0)
             grind)
          | exact superpose b1e89 b1e275076
          | (have j0 := b1e275076 X0
             grind)
          | exact resolve b1e275076 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e275076
        have b1e275101 : ∀ X0 : G, y ≠ (k y (τ X0)) ∨ y = (M.op (τ X0) x) ∨ y = (M.op y (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e275091 X0
             have i₂ := b1e120682
             grind)
          | exact superpose b1e120682 b1e275091
          | (have j0 := b1e275091 X0
             grind)
          | exact resolve b1e275091 b1e120682
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e275091
        have b1e276460 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 (k y y))) ∨ (k X0 (k y y)) = X0 ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e75197 (k y y) X0
             have i₂ := b1e19396 X0
             grind)
          | exact superpose b1e19396 b1e75197
          | (have j0 := b1e75197 (k y y) X0
             grind)
          | exact resolve b1e75197 b1e19396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19396
        have b1e276562 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 (k y y))) ∨ (k X0 (k y y)) = X0 := by
          intro X0
          first
          | (have j0 := b1e276460 X0
             grind)
          | (have r₁ := b1e276460 X0
             have r₂ := b1e124647
             grind)
          | exact resolve b1e276460 b1e124647
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e276460
        have b1e276648 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (k X0 (k y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e276562 X0
             have i₂ := b1e120682
             grind)
          | exact superpose b1e120682 b1e276562
          | (have j0 := b1e276562 X0
             grind)
          | exact resolve b1e276562 b1e120682
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e276562
        have b1e276700 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 x)) ∨ (k X0 (k y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e276648 X0
             have i₂ := b1e89 X0
             grind)
          | exact superpose b1e89 b1e276648
          | (have j0 := b1e276648 X0
             grind)
          | exact resolve b1e276648 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e276648
        have b1e276729 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 x)) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e276700 X0
             have i₂ := b1e120682
             grind)
          | exact superpose b1e120682 b1e276700
          | (have j0 := b1e276700 X0
             grind)
          | exact resolve b1e276700 b1e120682
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120682 b1e276700
        have b1e360898 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (M.op X2 X1)) ∨ (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op X2 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5231 X0 (M.op X2 X1)
             have i₂ := b1e41 X1 (σ X0) X2
             grind)
          | exact superpose b1e41 b1e5231
          | (have j0 := b1e5231 X0 (M.op X2 X1)
             grind)
          | exact resolve b1e5231 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5231
        have b1e428825 : ∀ X0 : G, x = (k x (k x X0)) ∨ (τ (τ x)) = (τ (k (τ x) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e75211 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e75211
          | (have j0 := b1e75211 (τ X0)
             grind)
          | exact resolve b1e75211 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75211
        have b1e428952 : ∀ X0 : G, (τ (τ x)) = (τ (τ (k x X0))) ∨ x = (k x (k x X0)) := by
          intro X0
          first
          | (have i₁ := b1e428825 X0
             have i₂ := b1e282 X0 x
             grind)
          | exact superpose b1e282 b1e428825
          | (have j0 := b1e428825 X0
             grind)
          | exact resolve b1e428825 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e428825
        have b1e429252 : ∀ X0 X1 : G, (k (τ X0) (τ (τ x))) = (τ (k X0 (τ (k x X1)))) ∨ x = (k x (k x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e282 (τ (k x X1)) X0
             have i₂ := b1e428952 X1
             grind)
          | exact superpose b1e428952 b1e282
          | (have j1 := b1e428952 X1
             grind)
          | exact resolve b1e282 b1e428952
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e428952
        have b1e429357 : ∀ X0 X1 : G, (τ (k X0 (τ x))) = (τ (k X0 (τ (k x X1)))) ∨ x = (k x (k x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e429252 X0 X1
             have i₂ := b1e282 (τ x) X0
             grind)
          | exact superpose b1e282 b1e429252
          | (have j0 := b1e429252 X0 X1
             grind)
          | exact resolve b1e429252 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e429252
        have b1e477538 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e219657 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e219657
          | exact resolve b1e219657 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e219657
        have b1e477782 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e477538 X0
             have i₂ := b1e29 X0 (τ X0)
             grind)
          | exact superpose b1e29 b1e477538
          | (have j0 := b1e477538 X0
             grind)
          | exact resolve b1e477538 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e477538
        have b1e477810 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e477782 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e477782
          | (have j0 := b1e477782 X0
             grind)
          | exact resolve b1e477782 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e477782
        have b1e483890 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e28 X0 (τ X0)
             have i₂ := b1e477810 (τ X0)
             grind)
          | exact superpose b1e477810 b1e28
          | (have j1 := b1e477810 (τ X0)
             grind)
          | exact resolve b1e28 b1e477810
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e477810
        have b1e484227 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b1e483890 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e483890
          | (have j0 := b1e483890 X0
             grind)
          | exact resolve b1e483890 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e483890
        have b1e519668 : ∀ X0 X1 : G, y = (k y (M.op (k y X0) X1)) ∨ y = (k y X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e6145 y x x x
             have i₂ := b1e120723
             grind)
          | exact superpose b1e120723 b1e6145
          | (have j0 := b1e6145 y X1 (M.op (k y X0) X1) x
             grind)
          | exact resolve b1e6145 b1e120723
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6145
        have b1e520883 : ∀ X0 X1 : G, y ≠ y ∨ y = (M.op (M.op (k y X0) X1) y) ∨ y = (M.op y (M.op (k y X0) X1)) ∨ y = (k y X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e1451 y (M.op (k y X0) X1)
             have i₂ := b1e519668 X0 X1
             grind)
          | exact superpose b1e519668 b1e1451
          | (have j0 := b1e1451 y (M.op (k y X0) X1)
             have j1 := b1e519668 X0 X1
             grind)
          | (have r₁ := b1e1451 y (M.op (k y X0) X1)
             have r₂ := b1e519668 X0 X1
             grind)
          | (have r₁ := b1e1451 y X0
             have r₂ := b1e519668 X0 X1
             grind)
          | exact resolve b1e1451 b1e519668
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e519668
        have b1e520886 : ∀ X0 X1 : G, y = (M.op (M.op (k y X0) X1) y) ∨ y = (M.op y (M.op (k y X0) X1)) ∨ y = (k y X0) := by
          intro X0 X1
          first
          | (have j0 := b1e520883 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e520883
        have b1e520893 : ∀ X0 X1 : G, y = (M.op (k y X0) y) ∨ y = (M.op y (M.op (k y X0) X1)) ∨ y = (k y X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e520886 X0 X1
             have i₂ := b1e42 (k y X0) X1 y
             grind)
          | exact superpose b1e42 b1e520886
          | (have j0 := b1e520886 X0 X1
             grind)
          | exact resolve b1e520886 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e520886
        have b1e520900 : ∀ X0 X1 : G, y = (M.op (k y X0) x) ∨ y = (M.op y (M.op (k y X0) X1)) ∨ y = (k y X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e520893 X0 X1
             have i₂ := b1e89 (k y X0)
             grind)
          | exact superpose b1e89 b1e520893
          | (have j0 := b1e520893 X0 X1
             grind)
          | exact resolve b1e520893 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e520893
        have b1e520903 : ∀ X0 X1 : G, y = (M.op (k y X0) x) ∨ y = (M.op y X1) ∨ y = (k y X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e520900 X0 X1
             have i₂ := b1e41 X1 y (k y X0)
             grind)
          | exact superpose b1e41 b1e520900
          | (have j0 := b1e520900 X0 X1
             grind)
          | exact resolve b1e520900 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e520900
        have b1e523528 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 y) ∨ y = (M.op (k y X2) x) ∨ y = (k y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e41 X1 X0 y
             have i₂ := b1e520903 X2 X1
             grind)
          | exact superpose b1e520903 b1e41
          | (have j1 := b1e520903 X2 X1
             grind)
          | exact resolve b1e41 b1e520903
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e523633 : ∀ X0 X1 X2 : G, y = (M.op (k y X2) x) ∨ (M.op X0 X1) = (M.op X0 x) ∨ y = (k y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e523528 X0 X1 X2
             have i₂ := b1e89 X0
             grind)
          | exact superpose b1e89 b1e523528
          | (have j0 := b1e523528 X0 X1 X2
             grind)
          | exact resolve b1e523528 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e523528
        have b1e548549 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X1))) = (k (M.op X0 X1) (τ (τ (M.op (σ (σ (M.op X0 X1))) X2)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e181 (M.op X0 X1) (τ (M.op (σ (σ (M.op X0 X1))) X2))
             have i₂ := b1e58222 X0 X1 X2
             grind)
          | exact superpose b1e58222 b1e181
          | exact resolve b1e181 b1e58222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58222
        have b1e548571 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (τ (τ (M.op (σ (σ (M.op X0 X1))) X2)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e548549 X0 X1 X2
             have i₂ := b1e13 (M.op X0 X1)
             grind)
          | exact superpose b1e13 b1e548549
          | exact resolve b1e548549 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e548549
        have b1e549674 : ∀ X0 : G, (σ (σ x)) = (k (σ (σ x)) (τ (τ (M.op (σ (σ (σ (σ x)))) X0)))) := by
          intro X0
          first
          | (have i₁ := b1e548571 (σ (σ x)) (σ (σ x)) x
             have i₂ := b1e2858
             grind)
          | exact superpose b1e2858 b1e548571
          | exact resolve b1e548571 b1e2858
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2858 b1e548571
        have b1e552657 : ∀ X0 : G, (τ (σ (σ x))) = (k (σ x) (τ (τ (τ (M.op (σ (σ (σ (σ x)))) X0))))) := by
          intro X0
          first
          | (have i₁ := b1e181 (σ x) (τ (τ (M.op (σ (σ (σ (σ x)))) X0)))
             have i₂ := b1e549674 X0
             grind)
          | exact superpose b1e549674 b1e181
          | exact resolve b1e181 b1e549674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e549674
        have b1e552680 : ∀ X0 : G, (σ x) = (k (σ x) (τ (τ (τ (M.op (σ (σ (σ (σ x)))) X0))))) := by
          intro X0
          first
          | (have i₁ := b1e552657 X0
             have i₂ := b1e13 (σ x)
             grind)
          | exact superpose b1e13 b1e552657
          | exact resolve b1e552657 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e552657
        have b1e555396 : ∀ X0 : G, (τ (σ x)) = (k x (τ (τ (τ (τ (M.op (σ (σ (σ (σ x)))) X0)))))) := by
          intro X0
          first
          | (have i₁ := b1e181 x (τ (τ (τ (M.op (σ (σ (σ (σ x)))) X0))))
             have i₂ := b1e552680 X0
             grind)
          | exact superpose b1e552680 b1e181
          | exact resolve b1e181 b1e552680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e555419 : ∀ X0 : G, x = (k x (τ (τ (τ (τ (M.op (σ (σ (σ (σ x)))) X0)))))) := by
          intro X0
          first
          | (have i₁ := b1e555396 X0
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e555396
          | exact resolve b1e555396 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e555396
        have b1e560668 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (σ (τ (k (M.op X0 X1) X2))) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e14 (k (k X0 X1) X2)
             have i₂ := b1e63886 X0 X1 X2
             grind)
          | exact superpose b1e63886 b1e14
          | (have j1 := b1e63886 X0 X1 X2
             grind)
          | exact resolve b1e14 b1e63886
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63886
        have b1e560736 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e560668 X0 X1 X2
             have i₂ := b1e14 (k (M.op X0 X1) X2)
             grind)
          | exact superpose b1e14 b1e560668
          | (have j0 := b1e560668 X0 X1 X2
             grind)
          | exact resolve b1e560668 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e560668
        have b1e566488 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (σ (τ (k X0 (M.op X1 X2)))) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e14 (k X0 (k X1 X2))
             have i₂ := b1e63887 X1 X2 X0
             grind)
          | exact superpose b1e63887 b1e14
          | (have j1 := b1e63887 X1 X2 X2
             grind)
          | exact resolve b1e14 b1e63887
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63887
        have b1e566566 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X1 X2)) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e566488 X0 X1 X2
             have i₂ := b1e14 (k X0 (M.op X1 X2))
             grind)
          | exact superpose b1e14 b1e566488
          | (have j0 := b1e566488 X0 X1 X2
             grind)
          | exact resolve b1e566488 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e566488
        have b1e567328 : ∀ X0 X1 : G, (k X0 X1) ≠ (k (k X0 X1) (M.op X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e922 (k X0 X1)
             have i₂ := b1e566566 (k X0 X1) X0 X1
             grind)
          | exact superpose b1e566566 b1e922
          | (have j0 := b1e922 (k X0 X1)
             have j1 := b1e566566 X0 X0 X1
             grind)
          | (have r₁ := b1e922 x
             have r₂ := b1e566566 X0 x x
             grind)
          | exact resolve b1e922 b1e566566
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e566566
        have b1e567719 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e567328 X0 X1
             have j1 := b1e10501 X0 X1 x
             grind)
          | (have r₁ := b1e567328 x X1
             have r₂ := b1e10501 x X1 x
             grind)
          | (have r₁ := b1e567328 X0 X1
             have r₂ := b1e10501 (k X0 X1) (M.op X0 X1) x
             grind)
          | exact resolve b1e567328 b1e10501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10501 b1e567328
        have b1e568492 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e5940 X0 X1 (k X0 X1)
             have i₂ := b1e567719 X0 X1
             grind)
          | exact superpose b1e567719 b1e5940
          | (have j0 := b1e5940 X0 X1 x
             have j1 := b1e567719 X0 X1
             grind)
          | exact resolve b1e5940 b1e567719
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e568569 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e568492 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e568492
        have b1e649240 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1640 X0 X1 (k X0 X1)
             have i₂ := b1e567719 X0 X1
             grind)
          | exact superpose b1e567719 b1e1640
          | (have j0 := b1e1640 X0 X1 x
             have j1 := b1e567719 X0 X1
             grind)
          | exact resolve b1e1640 b1e567719
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1640
        have b1e649487 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e649240 X0 X1
             have j1 := b1e1451 X0 X1
             grind)
          | (have r₁ := b1e649240 X0 X1
             have r₂ := b1e1451 X0 X1
             grind)
          | exact resolve b1e649240 b1e1451
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1451 b1e649240
        have b1e662380 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ (k X0 (k x (τ (τ (τ (τ (M.op (σ (σ (σ (σ x)))) X1)))))))) := by
          intro X0 X1
          first
          | (have i₁ := b1e15790 X0 x (τ (τ (τ (M.op (σ (σ (σ (σ x)))) X1))))
             have i₂ := b1e552680 X1
             grind)
          | exact superpose b1e552680 b1e15790
          | (have j0 := b1e15790 X0 x (τ (τ (τ (M.op (σ (σ (σ (σ x)))) X1))))
             grind)
          | exact resolve b1e15790 b1e552680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15790 b1e552680
        have b1e662423 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e662380 X0 x
             have i₂ := b1e555419 x
             grind)
          | exact superpose b1e555419 b1e662380
          | (have j0 := b1e662380 X0 x
             grind)
          | exact resolve b1e662380 b1e555419
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e555419 b1e662380
        have b1e702576 : ∀ X0 X1 : G, (τ (τ (σ (σ X0)))) = (k (τ (τ (σ (σ X0)))) X0) ∨ (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e2164 (σ (σ X0)) X0
             have i₂ := b1e83273 X0 X1
             grind)
          | exact superpose b1e83273 b1e2164
          | (have j1 := b1e83273 X0 X1
             grind)
          | exact resolve b1e2164 b1e83273
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2164 b1e83273
        have b1e702614 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e702576 X0 X1
             have i₂ := b1e13 (σ X0)
             grind)
          | exact superpose b1e13 b1e702576
          | (have j0 := b1e702576 X0 X1
             grind)
          | exact resolve b1e702576 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e702576
        have b1e702649 : ∀ X0 X1 : G, (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e702614 X0 X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e702614
          | (have j0 := b1e702614 X0 X1
             grind)
          | exact resolve b1e702614 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e702614
        have b1e702680 : ∀ X0 X1 : G, (M.op X1 (σ (σ (τ X0)))) = (M.op X1 (σ (k X0 (σ (τ X0))))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e702649 (τ X0) X1
             have i₂ := b1e28 X0 (τ X0)
             grind)
          | exact superpose b1e28 b1e702649
          | (have j0 := b1e702649 (τ X0) X1
             grind)
          | exact resolve b1e702649 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e702649
        have b1e702894 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e702680 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e702680
          | (have j0 := b1e702680 X0 X1
             grind)
          | exact resolve b1e702680 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e702680
        have b1e702898 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e702894 X0 X1
             have i₂ := b1e282 X0 X0
             grind)
          | exact superpose b1e282 b1e702894
          | (have j0 := b1e702894 X0 X1
             grind)
          | exact resolve b1e702894 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e702894
        have b1e703152 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) (τ X0))) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1215 (τ X0) X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1215
          | exact resolve b1e1215 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1215
        have b1e703222 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) (τ X0))) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e703152 X0 X1
             have i₂ := b1e28 X0 X1
             grind)
          | exact superpose b1e28 b1e703152
          | (have j0 := b1e703152 X0 X1
             grind)
          | exact resolve b1e703152 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703152
        have b1e703233 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e703222 X0 X1
             have i₂ := b1e29 X0 (τ X0)
             grind)
          | exact superpose b1e29 b1e703222
          | (have j0 := b1e703222 X0 X1
             grind)
          | exact resolve b1e703222 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703222
        have b1e703242 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 X0) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e703233 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e703233
          | (have j0 := b1e703233 X0 X1
             grind)
          | exact resolve b1e703233 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703233
        have b1e703478 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k X0 (σ (τ X0)))) ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e702898 (τ X0) X1
             have i₂ := b1e28 X0 (τ X0)
             grind)
          | exact superpose b1e28 b1e702898
          | (have j0 := b1e702898 (τ X0) X1
             grind)
          | exact resolve b1e702898 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e702898
        have b1e703695 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e703478 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e703478
          | (have j0 := b1e703478 X0 X1
             grind)
          | exact resolve b1e703478 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703478
        have b1e703700 : ∀ X0 X1 : G, (τ (τ X0)) = (τ (τ (k X0 X0))) ∨ (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e703695 X0 X1
             have i₂ := b1e282 X0 X0
             grind)
          | exact superpose b1e282 b1e703695
          | (have j0 := b1e703695 X0 X1
             grind)
          | exact resolve b1e703695 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e282 b1e703695
        have b1e703763 : ∀ X0 X1 : G, (τ (k X0 X0)) = (σ (τ (τ X0))) ∨ (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e14 (τ (k X0 X0))
             have i₂ := b1e703700 X0 X1
             grind)
          | exact superpose b1e703700 b1e14
          | (have j1 := b1e703700 X0 X1
             grind)
          | exact resolve b1e14 b1e703700
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703700
        have b1e703993 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e703763 X0 X1
             have i₂ := b1e14 (τ X0)
             grind)
          | exact superpose b1e14 b1e703763
          | (have j0 := b1e703763 X0 X1
             grind)
          | exact resolve b1e703763 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703763
        have b1e704041 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e703993 (σ X1) X1
             have i₂ := b1e18 X1 X1
             grind)
          | exact superpose b1e18 b1e703993
          | exact resolve b1e703993 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703993
        have b1e704344 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e704041 X0 X1
             have i₂ := b1e13 (k X0 X0)
             grind)
          | exact superpose b1e13 b1e704041
          | (have j0 := b1e704041 X0 X1
             grind)
          | exact resolve b1e704041 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e704041
        have b1e704352 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e704344 X0 X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e704344
          | (have j0 := b1e704344 X0 X1
             grind)
          | exact resolve b1e704344 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e704344
        have b1e704716 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e704352 X0 X1
             have i₂ := b1e75197 X0 X0
             grind)
          | exact superpose b1e75197 b1e704352
          | (have j0 := b1e704352 X0 X1
             have j1 := b1e75197 X0 X0
             grind)
          | exact resolve b1e704352 b1e75197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e704352
        have b1e704964 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e704716 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e704716
        have b1e704997 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e704964 (τ X0) X1
             have i₂ := b1e484227 X0
             grind)
          | exact superpose b1e484227 b1e704964
          | (have j0 := b1e704964 (τ X0) X1
             have j1 := b1e484227 X0
             grind)
          | exact resolve b1e704964 b1e484227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e484227 b1e704964
        have b1e705252 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e704997 X0 X1
             have j1 := b1e922 (τ X0)
             grind)
          | (have r₁ := b1e704997 X0 X1
             have r₂ := b1e922 (τ X0)
             grind)
          | exact resolve b1e704997 b1e922
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e704997
        have b1e705256 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e705252 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e705252
          | (have j0 := b1e705252 X0 X1
             grind)
          | exact resolve b1e705252 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e705252
        have b1e706514 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e916 (τ X0) (τ X0)
             have i₂ := b1e705256 X0 X1
             grind)
          | exact superpose b1e705256 b1e916
          | (have j1 := b1e705256 X0 X1
             grind)
          | exact resolve b1e916 b1e705256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e916 b1e705256
        have b1e706561 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e706514 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e706514
          | (have j0 := b1e706514 X0 X1
             grind)
          | exact resolve b1e706514 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e706514
        have b1e706774 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e706561 X0 (k X0 X0)
             have i₂ := b1e567719 X0 X0
             grind)
          | exact superpose b1e567719 b1e706561
          | (have j0 := b1e706561 X0 x
             have j1 := b1e567719 X0 X0
             grind)
          | exact resolve b1e706561 b1e567719
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e567719 b1e706561
        have b1e707117 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e706774 X0
             have j1 := b1e922 X0
             grind)
          | (have r₁ := b1e706774 X0
             have r₂ := b1e922 X0
             grind)
          | exact resolve b1e706774 b1e922
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e706774
        have b1e707264 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1072 (k X0 X0) X0
             have i₂ := b1e707117 X0
             grind)
          | exact superpose b1e707117 b1e1072
          | (have j1 := b1e707117 X0
             grind)
          | exact resolve b1e1072 b1e707117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e710659 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e707117 (k X0 X0)
             have i₂ := b1e707264 X0
             grind)
          | exact superpose b1e707264 b1e707117
          | (have j0 := b1e707117 (k X0 X0)
             have j1 := b1e707264 (k X0 X0)
             grind)
          | exact resolve b1e707117 b1e707264
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e707117 b1e707264
        have b1e710660 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e710659 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e710659
        have b1e711216 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1754 X0 X0 (k X0 X0)
             have i₂ := b1e710660 X0
             grind)
          | exact superpose b1e710660 b1e1754
          | (have j0 := b1e1754 X0 X0 x
             have j1 := b1e710660 X0
             grind)
          | exact resolve b1e1754 b1e710660
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1754 b1e710660
        have b1e711300 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e711216 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e711216
        have b1e724390 : ∀ X0 : G, y ≠ (k y X0) ∨ y = (M.op X0 x) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e275101 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e275101
          | exact resolve b1e275101 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e275101
        have b1e850947 : ∀ X0 X1 : G, y ≠ (M.op (k y X0) X1) ∨ y = (M.op (k y X0) x) ∨ y = (k y X0) := by
          intro X0 X1
          first
          | (have j0 := b1e523633 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e523633
        have b1e874739 : ∀ X0 X1 : G, y ≠ (M.op y X0) ∨ y = (M.op (k y X1) x) ∨ y = (k y X1) ∨ y = (k y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e850947 X1 X0
             have i₂ := b1e5940 y X1 X0
             grind)
          | exact superpose b1e5940 b1e850947
          | (have j0 := b1e850947 X1 X1
             have j1 := b1e5940 y X1 x
             grind)
          | exact resolve b1e850947 b1e5940
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5940 b1e850947
        have b1e874777 : ∀ X0 X1 : G, y ≠ (M.op y X0) ∨ y = (M.op (k y X1) x) ∨ y = (k y X1) := by
          intro X0 X1
          first
          | (have j0 := b1e874739 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e874739
        have b1e874781 : ∀ X1 : G, y = (M.op (k y X1) x) ∨ y = (k y X1) := by
          intro X1
          first
          | (have j0 := b1e874777 x X1
             have j1 := b1e520903 X1 X1
             grind)
          | (have r₁ := b1e874777 X1 X1
             have r₂ := b1e520903 x X1
             grind)
          | exact resolve b1e874777 b1e520903
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e520903 b1e874777
        have b1e962208 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e703242 X0 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e703242
          | (have j0 := b1e703242 X1 X1
             grind)
          | exact resolve b1e703242 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703242
        have b1e962434 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e711300 X1
             have i₂ := b1e962208 X0 X1
             grind)
          | exact superpose b1e962208 b1e711300
          | (have j0 := b1e711300 X0
             have j1 := b1e962208 X1 X0
             grind)
          | exact resolve b1e711300 b1e962208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e711300
        have b1e962466 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e962434 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e962434
        have b1e1028370 : ∀ X0 X1 : G, (σ (τ (k X0 (τ x)))) = (k X0 (τ (k x X1))) ∨ x = (k x (k x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e14 (k X0 (τ (k x X1)))
             have i₂ := b1e429357 X0 X1
             grind)
          | exact superpose b1e429357 b1e14
          | (have j1 := b1e429357 X0 X1
             grind)
          | exact resolve b1e14 b1e429357
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e429357
        have b1e1028371 : ∀ X0 X1 : G, (k X0 (τ x)) = (k X0 (τ (k x X1))) ∨ x = (k x (k x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1028370 X0 X1
             have i₂ := b1e14 (k X0 (τ x))
             grind)
          | exact superpose b1e14 b1e1028370
          | (have j0 := b1e1028370 X0 X1
             grind)
          | exact resolve b1e1028370 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1028370
        have b1e1028438 : ∀ X0 X1 : G, (σ (k (τ X0) (τ x))) = (k X0 (σ (τ (k x X1)))) ∨ x = (k x (k x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e28 X0 (τ (k x X1))
             have i₂ := b1e1028371 (τ X0) X1
             grind)
          | exact superpose b1e1028371 b1e28
          | (have j1 := b1e1028371 X0 X1
             grind)
          | exact resolve b1e28 b1e1028371
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e1028371
        have b1e1028477 : ∀ X0 X1 : G, (k X0 (k x X1)) = (σ (k (τ X0) (τ x))) ∨ x = (k x (k x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1028438 X0 X1
             have i₂ := b1e14 (k x X1)
             grind)
          | exact superpose b1e14 b1e1028438
          | (have j0 := b1e1028438 X0 X1
             grind)
          | exact resolve b1e1028438 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1028438
        have b1e1028485 : ∀ X0 X1 : G, (k X0 (k x X1)) = (k (σ (τ X0)) x) ∨ x = (k x (k x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1028477 X0 X1
             have i₂ := b1e29 x (τ X0)
             grind)
          | exact superpose b1e29 b1e1028477
          | (have j0 := b1e1028477 X0 X1
             grind)
          | exact resolve b1e1028477 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1028477
        have b1e1028486 : ∀ X0 X1 : G, (k X0 x) = (k X0 (k x X1)) ∨ x = (k x (k x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1028485 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e1028485
          | (have j0 := b1e1028485 X0 X1
             grind)
          | exact resolve b1e1028485 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1028485
        have b1e1029522 : ∀ X0 : G, x ≠ (k x x) ∨ x = (k x (k x X0)) := by
          intro X0
          first
          | (have j0 := b1e1028486 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1028486
        have b1e1029542 : ∀ X0 : G, x = (k x (k x X0)) := by
          intro X0
          first
          | (have j0 := b1e1029522 X0
             grind)
          | (have r₁ := b1e1029522 X0
             have r₂ := b1e65
             grind)
          | exact resolve b1e1029522 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e1029522
        have b1e1030343 : ∀ X0 : G, x = (M.op x (k x X0)) ∨ x = (M.op (k x X0) x) ∨ x = (M.op x (k x X0)) := by
          intro X0
          first
          | (have i₁ := b1e649487 x (k x X0)
             have i₂ := b1e1029542 X0
             grind)
          | exact superpose b1e1029542 b1e649487
          | (have j0 := b1e649487 x (k x X0)
             grind)
          | exact resolve b1e649487 b1e1029542
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e649487 b1e1029542
        have b1e1030360 : ∀ X0 : G, x = (M.op (k x X0) x) ∨ x = (M.op x (k x X0)) := by
          intro X0
          first
          | (have j0 := b1e1030343 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1030343
        have b1e1217630 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e21282 X0 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e21282
          | exact resolve b1e21282 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21282
        have b1e1217823 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e1217630 X2 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1217630
        have b1e1230511 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X2))) ∨ (τ (M.op (σ X0) X2)) = (k X0 (τ (M.op X1 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e181 X0 (M.op X1 X2)
             have i₂ := b1e360898 X0 X2 X1
             grind)
          | exact superpose b1e360898 b1e181
          | (have j1 := b1e360898 X0 X2 X1
             grind)
          | exact resolve b1e181 b1e360898
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e181 b1e360898
        have b1e1230512 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) X2)) = (k X0 (τ (M.op X1 X2))) ∨ (k X0 (τ (M.op X1 X2))) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1230511 X0 X1 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e1230511
          | (have j0 := b1e1230511 X0 X1 X2
             grind)
          | exact resolve b1e1230511 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230511
        have b1e1230591 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (M.op (σ X0) (σ y))) ∨ (k X0 (τ (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1230512 X0 (σ x) (σ y)
             have i₂ := b1e121852
             grind)
          | exact superpose b1e121852 b1e1230512
          | exact resolve b1e1230512 b1e121852
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121852
        have b1e1230592 : ∀ X0 : G, (τ (M.op (σ X0) (σ x))) = (k X0 (τ (σ x))) ∨ (k X0 (τ (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1230512 X0 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1230512
          | exact resolve b1e1230512 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230512
        have b1e1230637 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ X0) (σ x))) ∨ (k X0 (τ (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1230592 X0
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1230592
          | (have j0 := b1e1230592 X0
             grind)
          | exact resolve b1e1230592 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230592
        have b1e1230638 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ X0) (σ y))) ∨ (k X0 (τ (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1230591 X0
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e1230591
          | (have j0 := b1e1230591 X0
             grind)
          | exact resolve b1e1230591 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230591
        have b1e1230651 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ X0) (σ x))) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1230637 X0
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1230637
          | (have j0 := b1e1230637 X0
             grind)
          | exact resolve b1e1230637 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230637
        have b1e1230652 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ X0) (σ y))) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1230638 X0
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e1230638
          | (have j0 := b1e1230638 X0
             grind)
          | exact resolve b1e1230638 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230638
        have b1e1230924 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e14 (M.op (σ X0) (σ x))
             have i₂ := b1e1230651 X0
             grind)
          | exact superpose b1e1230651 b1e14
          | (have j1 := b1e1230651 X0
             grind)
          | exact resolve b1e14 b1e1230651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230651
        have b1e1231135 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k X0 x))) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e35 (σ x) (σ X0)
             have i₂ := b1e1230924 X0
             grind)
          | exact superpose b1e1230924 b1e35
          | (have j1 := b1e1230924 X0
             grind)
          | exact resolve b1e35 b1e1230924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e1230924
        have b1e1231168 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (k X0 x))) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1231135 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1231135
          | (have j0 := b1e1231135 X0
             grind)
          | exact resolve b1e1231135 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1231135
        have b1e1231421 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e14 (M.op (σ X0) (σ y))
             have i₂ := b1e1230652 X0
             grind)
          | exact superpose b1e1230652 b1e14
          | (have j1 := b1e1230652 X0
             grind)
          | exact resolve b1e14 b1e1230652
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230652
        have b1e1231513 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op X0 x))) ∨ (k X0 x) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1231168 X0
             have i₂ := b1e75197 x X0
             grind)
          | exact superpose b1e75197 b1e1231168
          | (have j0 := b1e1231168 X0
             have j1 := b1e75197 x X0
             grind)
          | exact resolve b1e1231168 b1e75197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75197 b1e1231168
        have b1e1231735 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op X0 x))) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b1e1231513 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1231513
        have b1e1231990 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (k X0 y))) ∨ (k X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e41 (σ y) X1 (σ X0)
             have i₂ := b1e1231421 X0
             grind)
          | exact superpose b1e1231421 b1e41
          | (have j1 := b1e1231421 X0
             grind)
          | exact resolve b1e41 b1e1231421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1231421
        have b1e1232096 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k y X0) = (k (k y X0) x) ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e1231735 (k y X0)
             have i₂ := b1e874781 X0
             grind)
          | exact superpose b1e874781 b1e1231735
          | (have j0 := b1e1231735 (k y X0)
             have j1 := b1e874781 X0
             grind)
          | exact resolve b1e1231735 b1e874781
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e874781
        have b1e1232404 : ∀ X0 : G, (k y X0) = (k (k y X0) x) ∨ y = (k y X0) := by
          intro X0
          first
          | (have j0 := b1e1232096 X0
             grind)
          | (have r₁ := b1e1232096 X0
             have r₂ := b1e21
             grind)
          | exact resolve b1e1232096 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1232096
        have b1e1232755 : ∀ X0 : G, (k y X0) = (k (M.op y X0) x) ∨ y = (k y X0) ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e560736 y X0 x
             have i₂ := b1e1232404 X0
             grind)
          | exact superpose b1e1232404 b1e560736
          | (have j0 := b1e560736 y X0 x
             have j1 := b1e1232404 X0
             grind)
          | exact resolve b1e560736 b1e1232404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e560736 b1e1232404
        have b1e1232760 : ∀ X0 : G, (k y X0) = (k (M.op y X0) x) ∨ y = (k y X0) := by
          intro X0
          first
          | (have j0 := b1e1232755 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1232755
        have b1e1237045 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op X0 x))) ∨ (k X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1231990 X0 X1
             have i₂ := b1e276729 X0
             grind)
          | exact superpose b1e276729 b1e1231990
          | (have j0 := b1e1231990 X0 X1
             have j1 := b1e276729 X0
             grind)
          | exact resolve b1e1231990 b1e276729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e276729 b1e1231990
        have b1e1237229 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op X0 x))) ∨ (k X0 y) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e1237045 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1237045
        have b1e1237845 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1231735 X0
             have i₂ := b1e1237229 X0 (σ x)
             grind)
          | exact superpose b1e1237229 b1e1231735
          | (have j0 := b1e1231735 X0
             have j1 := b1e1237229 X0 x
             grind)
          | exact resolve b1e1231735 b1e1237229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1231735 b1e1237229
        have b1e1237967 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b1e1237845 X0
             grind)
          | (have r₁ := b1e1237845 X0
             have r₂ := b1e21
             grind)
          | exact resolve b1e1237845 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1237845
        have b1e1238318 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 y) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e962208 y X0
             have i₂ := b1e1237967 X0
             grind)
          | exact superpose b1e1237967 b1e962208
          | (have j0 := b1e962208 y X0
             have j1 := b1e1237967 X0
             grind)
          | exact resolve b1e962208 b1e1237967
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e962208 b1e1237967
        have b1e1238547 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b1e1238318 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1238318
        have b1e1238614 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1238547 X0
             have i₂ := b1e89 X0
             grind)
          | exact superpose b1e89 b1e1238547
          | (have j0 := b1e1238547 X0
             grind)
          | exact resolve b1e1238547 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1238547
        have b1e1238672 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b1e1238614 X0
             have j1 := b1e15 X0 X0
             grind)
          | (have r₁ := b1e1238614 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e1238614 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1238614
        have b1e1240811 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 x) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e962466 X0 x
             have i₂ := b1e1238672 X0
             grind)
          | exact superpose b1e1238672 b1e962466
          | (have j0 := b1e962466 X0 x
             have j1 := b1e1238672 X0
             grind)
          | exact resolve b1e962466 b1e1238672
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e962466 b1e1238672
        have b1e1240816 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e1240811 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1240811
        have b1e1240888 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e1240816 X0
             have j1 := b1e922 X0
             grind)
          | (have r₁ := b1e1240816 X0
             have r₂ := b1e922 X0
             grind)
          | exact resolve b1e1240816 b1e922
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1240816
        have b1e1243561 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1072 X0 x
             have i₂ := b1e1240888 X0
             grind)
          | exact superpose b1e1240888 b1e1072
          | (have j1 := b1e1240888 X0
             grind)
          | exact resolve b1e1072 b1e1240888
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1072 b1e1240888
        have b1e1244999 : ∀ X0 : G, (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e1243561 X0
             have j1 := b1e922 X0
             grind)
          | (have r₁ := b1e1243561 X0
             have r₂ := b1e922 X0
             grind)
          | exact resolve b1e1243561 b1e922
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e922 b1e1243561
        have b1e1245402 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e31198 X1 X0
             have i₂ := b1e1244999 X0
             grind)
          | exact superpose b1e1244999 b1e31198
          | (have j0 := b1e31198 X1 X0
             grind)
          | exact resolve b1e31198 b1e1244999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31198
        have b1e1245550 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12692 X0 X1 X0
             have i₂ := b1e1244999 X0
             grind)
          | exact superpose b1e1244999 b1e12692
          | (have j0 := b1e12692 X0 X1 x
             grind)
          | exact resolve b1e12692 b1e1244999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12692
        have b1e1245935 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e1217823 X0 X0 x
             have i₂ := b1e1244999 X0
             grind)
          | exact superpose b1e1244999 b1e1217823
          | exact resolve b1e1217823 b1e1244999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1217823 b1e1244999
        have b1e1249051 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e1245550 X0 X1
             have j1 := b1e1245935 X1 X0
             grind)
          | (have r₁ := b1e1245550 X0 X0
             have r₂ := b1e1245935 X0 X0
             grind)
          | (have r₁ := b1e1245550 X1 X0
             have r₂ := b1e1245935 X0 X1
             grind)
          | exact resolve b1e1245550 b1e1245935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1245550
        have b1e1249059 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e1245402 X0 X1
             have j1 := b1e1245935 X1 X0
             grind)
          | (have r₁ := b1e1245402 X1 X0
             have r₂ := b1e1245935 X0 X1
             grind)
          | exact resolve b1e1245402 b1e1245935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1245402 b1e1245935
        have b1e1295506 : ∀ X0 : G, (k y X0) = (M.op (M.op y X0) x) ∨ y = (k y X0) ∨ x = (M.op (M.op y X0) x) := by
          intro X0
          first
          | (have i₁ := b1e1232760 X0
             have i₂ := b1e1249051 x (M.op y X0)
             grind)
          | exact superpose b1e1249051 b1e1232760
          | (have j0 := b1e1232760 X0
             have j1 := b1e1249051 x (M.op y X0)
             grind)
          | exact resolve b1e1232760 b1e1249051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1232760 b1e1249051
        have b1e1296231 : ∀ X0 : G, (k y X0) = (M.op y y) ∨ y = (k y X0) ∨ x = (M.op (M.op y X0) x) := by
          intro X0
          first
          | (have i₁ := b1e1295506 X0
             have i₂ := b1e37 y X0
             grind)
          | exact superpose b1e37 b1e1295506
          | (have j0 := b1e1295506 X0
             grind)
          | exact resolve b1e1295506 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1295506
        have b1e1296491 : ∀ X0 : G, (M.op y x) = (k y X0) ∨ y = (k y X0) ∨ x = (M.op (M.op y X0) x) := by
          intro X0
          first
          | (have i₁ := b1e1296231 X0
             have i₂ := b1e89 y
             grind)
          | exact superpose b1e89 b1e1296231
          | (have j0 := b1e1296231 X0
             grind)
          | exact resolve b1e1296231 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1296231
        have b1e1296585 : ∀ X0 : G, y = (k y X0) ∨ y = (k y X0) ∨ x = (M.op (M.op y X0) x) := by
          intro X0
          first
          | (have i₁ := b1e1296491 X0
             have i₂ := b1e120723
             grind)
          | exact superpose b1e120723 b1e1296491
          | (have j0 := b1e1296491 X0
             grind)
          | exact resolve b1e1296491 b1e120723
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1296491
        have b1e1296586 : ∀ X0 : G, y = (k y X0) ∨ x = (M.op (M.op y X0) x) := by
          intro X0
          first
          | (have j0 := b1e1296585 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1296585
        have b1e1296628 : ∀ X0 : G, x = (M.op y y) ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e1296586 X0
             have i₂ := b1e37 y X0
             grind)
          | exact superpose b1e37 b1e1296586
          | (have j0 := b1e1296586 X0
             grind)
          | exact resolve b1e1296586 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e1296586
        have b1e1296638 : ∀ X0 : G, x = (M.op y x) ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e1296628 X0
             have i₂ := b1e89 y
             grind)
          | exact superpose b1e89 b1e1296628
          | (have j0 := b1e1296628 X0
             grind)
          | exact resolve b1e1296628 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1296628
        have b1e1296642 : ∀ X0 : G, y = (k y X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e1296638 X0
             have i₂ := b1e120723
             grind)
          | exact superpose b1e120723 b1e1296638
          | (have j0 := b1e1296638 X0
             grind)
          | exact resolve b1e1296638 b1e120723
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120723 b1e1296638
        have b1e1297017 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 x) ∨ y = (M.op y X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e724390 X0
             have i₂ := b1e1296642 X0
             grind)
          | exact superpose b1e1296642 b1e724390
          | (have j0 := b1e724390 X0
             grind)
          | (have r₁ := b1e724390 X0
             have r₂ := b1e1296642 X0
             grind)
          | exact resolve b1e724390 b1e1296642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e724390
        have b1e1297779 : ∀ X0 X1 : G, y = (M.op y X0) ∨ y = (M.op X1 y) ∨ y = (M.op y X0) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b1e17482 y X0 X1
             have i₂ := b1e1296642 (M.op X1 X0)
             grind)
          | exact superpose b1e1296642 b1e17482
          | (have j0 := b1e17482 y X0 X1
             grind)
          | exact resolve b1e17482 b1e1296642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17482 b1e1296642
        have b1e1298743 : ∀ X0 X1 : G, y = (M.op y X0) ∨ y = (M.op X1 y) ∨ x = y := by
          intro X0 X1
          first
          | (have j0 := b1e1297779 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1297779
        have b1e1298853 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op X0 x) ∨ x = y := by
          intro X0
          first
          | (have j0 := b1e1297017 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1297017
        have b1e1298937 : ∀ X0 X1 : G, y = (M.op y X0) ∨ y = (M.op X1 x) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b1e1298743 X0 X1
             have i₂ := b1e89 X1
             grind)
          | exact superpose b1e89 b1e1298743
          | (have j0 := b1e1298743 X0 X1
             grind)
          | exact resolve b1e1298743 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1298743
        have b1e1394974 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op X0 x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e34 X0 y
             have i₂ := b1e1298853 X0
             grind)
          | exact superpose b1e1298853 b1e34
          | (have j1 := b1e1298853 X0
             grind)
          | exact resolve b1e34 b1e1298853
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e1298853
        have b1e1395352 : ∀ X0 : G, y = (M.op X0 x) ∨ x = (M.op x X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e1394974 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1394974
          | (have j0 := b1e1394974 X0
             grind)
          | exact resolve b1e1394974 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1394974
        have b1e1400444 : ∀ X0 : G, x = y ∨ x = (M.op x (k x X0)) ∨ x = (M.op x (k x X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e1030360 X0
             have i₂ := b1e1395352 (k x X0)
             grind)
          | exact superpose b1e1395352 b1e1030360
          | (have j0 := b1e1030360 X0
             have j1 := b1e1395352 (k x X0)
             grind)
          | exact resolve b1e1030360 b1e1395352
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1030360 b1e1395352
        have b1e1400617 : ∀ X0 : G, x = (M.op x (k x X0)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b1e1400444 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1400444
        have b1e1401775 : ∀ X0 : G, x = (k x X0) ∨ x = (k x X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e568569 x X0
             have i₂ := b1e1400617 X0
             grind)
          | exact superpose b1e1400617 b1e568569
          | (have j0 := b1e568569 x X0
             grind)
          | exact resolve b1e568569 b1e1400617
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e568569 b1e1400617
        have b1e1402282 : ∀ X0 : G, x = (k x X0) ∨ x = y := by
          intro X0
          first
          | (have j0 := b1e1401775 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1401775
        have b1e1403632 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e29 X0 x
             have i₂ := b1e1402282 (τ X0)
             grind)
          | exact superpose b1e1402282 b1e29
          | exact resolve b1e29 b1e1402282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e1402282
        have b1e1408387 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e18 x X0
             have i₂ := b1e1403632 (σ X0)
             grind)
          | exact superpose b1e1403632 b1e18
          | exact resolve b1e18 b1e1403632
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1403632
        have b1e1411131 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k (k x X0) x)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e662423 (k x X0)
             have i₂ := b1e1408387 X0
             grind)
          | exact superpose b1e1408387 b1e662423
          | (have j0 := b1e662423 x
             grind)
          | exact resolve b1e662423 b1e1408387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e662423 b1e1408387
        have b1e1411242 : ∀ X0 : G, (σ x) = (σ (k (k x X0) x)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b1e1411131 X0
             grind)
          | (have r₁ := b1e1411131 X0
             have r₂ := b1e188
             grind)
          | exact resolve b1e1411131 b1e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1411131
        have b1e1425994 : ∀ X0 : G, (τ (σ x)) = (k (k x X0) x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e13 (k (k x X0) x)
             have i₂ := b1e1411242 X0
             grind)
          | exact superpose b1e1411242 b1e13
          | exact resolve b1e13 b1e1411242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1411242
        have b1e1426161 : ∀ X0 : G, x = (k (k x X0) x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e1425994 X0
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1425994
          | exact resolve b1e1425994 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1425994
        have b1e1428745 : ∀ X0 : G, x ≠ x ∨ x = (M.op (k x X0) x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e1249059 x (k x X0)
             have i₂ := b1e1426161 X0
             grind)
          | exact superpose b1e1426161 b1e1249059
          | (have r₁ := b1e1249059 x (k x X0)
             have r₂ := b1e1426161 X0
             grind)
          | exact resolve b1e1249059 b1e1426161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1249059 b1e1426161
        have b1e1428746 : ∀ X0 : G, x = (M.op (k x X0) x) ∨ x = y := by
          intro X0
          first
          | (have j0 := b1e1428745 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1428745
        have b1e1430148 : ∀ X1 : G, x = y ∨ y = (M.op y X1) ∨ x = y ∨ x = y := by
          intro X1
          first
          | (have i₁ := b1e1298937 X1 (k x x)
             have i₂ := b1e1428746 x
             grind)
          | exact superpose b1e1428746 b1e1298937
          | (have j0 := b1e1298937 X1 X1
             grind)
          | exact resolve b1e1298937 b1e1428746
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1298937 b1e1428746
        have b1e1430435 : ∀ X1 : G, y = (M.op y X1) ∨ x = y := by
          intro X1
          first
          | (have j0 := b1e1430148 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1430148
        have b1e1430928 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b1e41 X1 X0 y
             have i₂ := b1e1430435 X1
             grind)
          | exact superpose b1e1430435 b1e41
          | exact resolve b1e41 b1e1430435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e1430435
        have b1e1432517 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b1e1430928 X0 X1
             have i₂ := b1e89 X0
             grind)
          | exact superpose b1e89 b1e1430928
          | exact resolve b1e1430928 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89 b1e1430928
        have b1e1448757 : (σ x) = (M.op (σ x) x) ∨ x = y := by
          first
          | (have i₁ := b1e188
             have i₂ := b1e1432517 (σ x) (σ x)
             grind)
          | exact superpose b1e1432517 b1e188
          | exact resolve b1e188 b1e1432517
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e188
        have b1e1448758 : (σ x) ≠ (M.op (σ x) x) ∨ x = y := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1432517 (σ x) (σ y)
             grind)
          | exact superpose b1e1432517 b1e21
          | exact resolve b1e21 b1e1432517
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1432517
        have b1e1450588 : x = y := by
          first
          | (have r₁ := b1e1448757
             have r₂ := b1e1448758
             grind)
          | exact resolve b1e1448757 b1e1448758
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1448757 b1e1448758
        have b1e1450926 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e124647
             have i₂ := b1e1450588
             grind)
          | exact superpose b1e1450588 b1e124647
          | exact resolve b1e124647 b1e1450588
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124647 b1e1450588
        have b1e1453060 : False := by grind
        exact b1e1453060
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x ≠ x ∨ x = (k x y) := by
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
        have b2e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e277 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          | exact resolve b2e22 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e293 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e277
        have b2e298 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e293
             have r₂ := b2e21
             grind)
          | exact resolve b2e293 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e293
        have b2e308 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e298
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e298
          | exact resolve b2e298 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e298
        have b2e310 : False := by grind
        exact b2e310
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y x) := by grind
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
        have b3e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e36 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
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
        have b3e38 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
        have b3e39 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) x) := by
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
        have b3e41 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
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
        have b3e42 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e15 (M.op X0 X2) (M.op X3 X1)
             have i₂ := b3e12 X0 X1 X2 X3
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 (M.op X0 X2) (M.op X3 X1)
             grind)
          | (have r₁ := b3e15 (M.op X0 X1) (M.op X3 X1)
             have r₂ := b3e12 X0 X1 X1 X3
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b3e41 x X1 X2 X3 x
             have i₂ := b3e12 X2 X1 x x
             grind)
          | exact superpose b3e12 b3e41
          | exact resolve b3e41 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e44 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e38 X0 x X2 X3 x
             have i₂ := b3e12 X0 X3 x x
             grind)
          | exact superpose b3e12 b3e38
          | exact resolve b3e38 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e47 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (M.op (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X3 X1) = (k (M.op X3 X1) (M.op X0 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e16 (M.op X3 X1) (M.op X0 X2)
             have i₂ := b3e12 X0 X1 X2 X3
             grind)
          | exact superpose b3e12 b3e16
          | (have j0 := b3e16 (M.op X3 X1) (M.op X0 X2)
             grind)
          | (have r₁ := b3e16 (M.op X0 X1) (M.op X0 X2)
             have r₂ := b3e12 X0 X1 X2 X0
             grind)
          | exact resolve b3e16 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (k (M.op X3 X1) (M.op X0 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b3e47 X0 X1 X2 X3
             have j1 := b3e15 (M.op X3 X1) (M.op X0 X2)
             grind)
          | (have r₁ := b3e47 X0 X1 X2 X3
             have r₂ := b3e15 (M.op X3 X1) (M.op X0 X2)
             grind)
          | exact resolve b3e47 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b3e60 : (M.op y (σ y)) = (M.op x (σ x)) := by
          first
          | (have i₁ := b3e36 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e36
          | exact resolve b3e36 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e62 : x = (M.op x x) := by
          first
          | (have i₁ := b3e36 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e36
          | exact resolve b3e36 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e12 x X1 (M.op x X0) X3
             have i₂ := b3e36 X0 x
             grind)
          | exact superpose b3e36 b3e12
          | exact resolve b3e12 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e67 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b3e65 x X1 x
             have i₂ := b3e12 y X1 x x
             grind)
          | exact superpose b3e12 b3e65
          | exact resolve b3e65 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e90 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b3e15 x x
             have i₂ := b3e62
             grind)
          | exact superpose b3e62 b3e15
          | (have j0 := b3e15 x x
             grind)
          | (have r₁ := b3e15 x x
             have r₂ := b3e62
             grind)
          | exact resolve b3e15 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e91 : x = (k x x) := by grind
        clear b3e90
        have b3e95 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e43 (σ y) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e101 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X0 (M.op X2 X1)
             have i₂ := b3e43 X1 X0 X2
             grind)
          | exact superpose b3e43 b3e15
          | (have j0 := b3e15 X0 X1
             grind)
          | exact resolve b3e15 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e102 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (M.op (M.op X2 X1) X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 (M.op X2 X1) X0
             have i₂ := b3e43 X1 X0 X2
             grind)
          | exact superpose b3e43 b3e16
          | (have j0 := b3e16 (M.op X2 X1) X0
             grind)
          | (have r₁ := b3e16 (M.op X2 X1) X2
             have r₂ := b3e43 X1 X2 X2
             grind)
          | exact resolve b3e16 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e108 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e102 X0 X1 X2
             have j1 := b3e15 (M.op X2 X1) X0
             grind)
          | (have r₁ := b3e102 X1 X1 X2
             have r₂ := b3e15 (M.op X2 X1) X1
             grind)
          | exact resolve b3e102 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102
        have b3e130 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X0 X2)) = X1 ∨ (k X1 (M.op X0 X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X1 (M.op X0 X2)
             have i₂ := b3e44 X0 X2 X1
             grind)
          | exact superpose b3e44 b3e16
          | (have j0 := b3e16 X1 (M.op X0 X2)
             grind)
          | exact resolve b3e16 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e137 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have j0 := b3e130 X0 X1 X2
             have j1 := b3e15 X1 (M.op X0 X2)
             grind)
          | (have r₁ := b3e130 X0 X0 X2
             have r₂ := b3e15 X0 (M.op X0 X2)
             grind)
          | exact resolve b3e130 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130
        have b3e150 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e67 X0
             grind)
          | exact superpose b3e67 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | exact resolve b3e16 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e158 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e150 X0
             have j1 := b3e15 X0 y
             grind)
          | (have r₁ := b3e150 X0
             have r₂ := b3e15 X0 y
             grind)
          | exact resolve b3e150 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e150
        have b3e161 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e28 X0 X1
             have i₂ := b3e17 (τ X0) X1
             grind)
          | exact superpose b3e17 b3e28
          | (have j1 := b3e17 (τ X0) X1
             grind)
          | exact resolve b3e28 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e164 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e28 X0 X1
             grind)
          | exact superpose b3e28 b3e13
          | exact resolve b3e13 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e186 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e18 (k X0 (τ X1)) X2
             have i₂ := b3e29 X1 X0
             grind)
          | exact superpose b3e29 b3e18
          | exact resolve b3e18 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e187 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e29 X1 X0
             grind)
          | exact superpose b3e29 b3e13
          | exact resolve b3e13 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e197 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e16 (σ y) X0
             have i₂ := b3e95 X0
             grind)
          | exact superpose b3e95 b3e16
          | (have j0 := b3e16 (σ y) X0
             grind)
          | exact resolve b3e16 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e203 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e95 (σ x)
             grind)
          | exact superpose b3e95 b3e22
          | exact resolve b3e22 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e209 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ x)) ∨ (σ y) = (k (σ y) X0) := by
          intro X0
          first
          | (have j0 := b3e197 X0
             have j1 := b3e15 (σ y) X0
             grind)
          | (have r₁ := b3e197 x
             have r₂ := b3e15 (σ y) x
             grind)
          | exact resolve b3e197 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e197
        have b3e286 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e164 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e164
          | exact resolve b3e164 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e340 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e42 X0 X1 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e404 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e49 X0 X1 X2 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e451 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e54 X0 y
             have i₂ := b3e95 (σ X0)
             grind)
          | exact superpose b3e95 b3e54
          | (have j0 := b3e54 X0 y
             grind)
          | exact resolve b3e54 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e482 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 (σ X0) (σ X1)
             have i₂ := b3e54 X0 X1
             grind)
          | exact superpose b3e54 b3e16
          | (have j0 := b3e16 (σ X0) (σ X1)
             have j1 := b3e54 X0 X1
             grind)
          | (have r₁ := b3e16 (σ X0) (σ X1)
             have r₂ := b3e54 X0 X1
             grind)
          | (have r₁ := b3e16 (σ X0) (σ X0)
             have r₂ := b3e54 X0 X0
             grind)
          | exact resolve b3e16 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e488 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op (σ X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e44 (σ X1) (σ X0) X2
             have i₂ := b3e54 X0 X1
             grind)
          | exact superpose b3e54 b3e44
          | (have j1 := b3e54 X0 X1
             grind)
          | exact resolve b3e44 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e491 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e54 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e492 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e493 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e491 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e491
        have b3e494 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e482 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e482
        have b3e495 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e494 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e494
        have b3e498 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e495 X0 X1
             have j1 := b3e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b3e495 X0 X1
             have r₂ := b3e15 (σ X0) (σ X1)
             grind)
          | exact resolve b3e495 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e495
        have b3e515 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e498 X0 X1
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e498
          | (have j0 := b3e498 X0 X1
             grind)
          | exact resolve b3e498 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e498
        have b3e536 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e340 (σ x) (σ x) x
             have i₂ := b3e203
             grind)
          | exact superpose b3e203 b3e340
          | exact resolve b3e340 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e539 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (k (σ (k X0 X1)) (M.op X2 (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e340 (σ X0) (σ X1) X2
             have i₂ := b3e54 X0 X1
             grind)
          | exact superpose b3e54 b3e340
          | (have j1 := b3e54 X0 X1
             grind)
          | exact resolve b3e340 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e766 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e187 x (M.op X0 (σ x))
             have i₂ := b3e536 X0
             grind)
          | exact superpose b3e536 b3e187
          | exact resolve b3e187 b3e536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e771 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e766 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e766
          | exact resolve b3e766 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e766
        have b3e911 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (M.op (σ X0) X1) (σ X2)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e186 X0 X1 X2
             have i₂ := b3e17 (σ X0) X1
             grind)
          | exact superpose b3e17 b3e186
          | (have j1 := b3e17 (σ X0) X1
             grind)
          | exact resolve b3e186 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e186
        have b3e939 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e493 (M.op X0 X1)
             have i₂ := b3e404 X0 X1 X1
             grind)
          | exact superpose b3e404 b3e493
          | (have j0 := b3e493 (M.op X0 X1)
             grind)
          | exact resolve b3e493 b3e404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e944 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e493 (τ X0)
             have i₂ := b3e29 X0 (τ X0)
             grind)
          | exact superpose b3e29 b3e493
          | (have j0 := b3e493 (τ X0)
             grind)
          | exact resolve b3e493 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e493
        have b3e946 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have j0 := b3e939 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e939
        have b3e949 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e944 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e944
          | (have j0 := b3e944 X0
             grind)
          | exact resolve b3e944 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e944
        have b3e952 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e949 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e949
          | (have j0 := b3e949 X0
             grind)
          | exact resolve b3e949 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e949
        have b3e960 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b3e952 (τ X0)
             have i₂ := b3e286 X0 X0
             grind)
          | exact superpose b3e286 b3e952
          | (have j0 := b3e952 (τ X0)
             grind)
          | exact resolve b3e952 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1101 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b3e108 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1248 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e515 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e515
          | exact resolve b3e515 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1265 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 y)) ∨ (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e95 (σ X0)
             have i₂ := b3e515 X0 y
             grind)
          | exact superpose b3e515 b3e95
          | (have j1 := b3e515 X0 y
             grind)
          | exact resolve b3e95 b3e515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1279 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e43 (σ X1) X2 (σ X0)
             have i₂ := b3e515 X0 X1
             grind)
          | exact superpose b3e515 b3e43
          | (have j1 := b3e515 X0 X1
             grind)
          | exact resolve b3e43 b3e515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1280 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e44 (σ X0) (σ X1) X2
             have i₂ := b3e515 X0 X1
             grind)
          | exact superpose b3e515 b3e44
          | (have j1 := b3e515 X0 X1
             grind)
          | exact resolve b3e44 b3e515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1291 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (k (σ (k X0 X1)) (M.op X2 (σ X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e340 (σ X0) (σ X1) X2
             have i₂ := b3e515 X0 X1
             grind)
          | exact superpose b3e515 b3e340
          | (have j1 := b3e515 X0 X1
             grind)
          | exact resolve b3e340 b3e515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1293 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (k (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e404 (σ X0) (σ X1) X2
             have i₂ := b3e515 X0 X1
             grind)
          | exact superpose b3e515 b3e404
          | (have j1 := b3e515 X0 X1
             grind)
          | exact resolve b3e404 b3e515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e515
        have b3e1315 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1248 X0 X1
             have i₂ := b3e28 X0 X1
             grind)
          | exact superpose b3e28 b3e1248
          | (have j0 := b3e1248 X0 X1
             grind)
          | exact resolve b3e1248 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1248
        have b3e1320 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1315 X0 X1
             have i₂ := b3e28 X0 X1
             grind)
          | exact superpose b3e28 b3e1315
          | (have j0 := b3e1315 X0 X1
             grind)
          | exact resolve b3e1315 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1315
        have b3e1386 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e492 (τ X0) (τ X1)
             have i₂ := b3e286 X1 X0
             grind)
          | exact superpose b3e286 b3e492
          | (have j0 := b3e492 (τ X0) (τ X1)
             grind)
          | exact resolve b3e492 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1419 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1386 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e1386
          | (have j0 := b3e1386 X0 X1
             grind)
          | exact resolve b3e1386 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1386
        have b3e1425 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1419 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1419
          | (have j0 := b3e1419 X0 X1
             grind)
          | exact resolve b3e1419 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1419
        have b3e1428 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1425 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1425
          | (have j0 := b3e1425 X0 X1
             grind)
          | exact resolve b3e1425 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1425
        have b3e1430 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1428 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e1428
          | (have j0 := b3e1428 X0 X1
             grind)
          | exact resolve b3e1428 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1428
        have b3e1432 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1430 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e1430
          | (have j0 := b3e1430 X0 X1
             grind)
          | exact resolve b3e1430 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1430
        have b3e1433 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1432 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1432
          | (have j0 := b3e1432 X0 X1
             grind)
          | exact resolve b3e1432 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1432
        have b3e1448 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op X2 X1))) ∨ (τ X0) = (M.op (M.op X2 X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e161 X0 (M.op x X1)
             have i₂ := b3e43 X1 (τ X0) x
             grind)
          | exact superpose b3e43 b3e161
          | (have j0 := b3e161 X0 (M.op X2 X1)
             grind)
          | exact resolve b3e161 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e161
        have b3e1480 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op X2 X1))) ∨ (τ X0) = (M.op X2 (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1448 X0 X1 X2
             have i₂ := b3e44 X2 X1 (τ X0)
             grind)
          | exact superpose b3e44 b3e1448
          | (have j0 := b3e1448 X0 X1 X2
             grind)
          | exact resolve b3e1448 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1448
        have b3e1760 : ∀ X0 X1 : G, (M.op (σ X0) (σ x)) = (σ (k X0 y)) ∨ (M.op (σ X0) X1) = (M.op (σ y) X1) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e488 X0 y x
             have i₂ := b3e95 (σ X0)
             grind)
          | exact superpose b3e95 b3e488
          | (have j0 := b3e488 X0 y X1
             grind)
          | exact resolve b3e488 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1762 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (σ X2) X1) ∨ (M.op X0 (σ X2)) = (σ (k (τ X0) X2)) ∨ (M.op X0 (σ X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e488 (τ X0) X1 X2
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e488
          | exact resolve b3e488 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1936 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) X2) = (M.op (σ X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e488 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1937 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e488 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e488
        have b3e1986 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (M.op X0 X1) = (M.op (σ X2) X1) ∨ (M.op X0 (σ X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1762 X0 X1 X2
             have i₂ := b3e28 X0 X2
             grind)
          | exact superpose b3e28 b3e1762
          | (have j0 := b3e1762 X0 X1 X2
             grind)
          | exact resolve b3e1762 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1762
        have b3e3086 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) (M.op X2 (σ (M.op X0 X1)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e340 (σ (M.op X0 X1)) (σ (M.op X0 X1)) X2
             have i₂ := b3e946 X0 X1
             grind)
          | exact superpose b3e946 b3e340
          | exact resolve b3e340 b3e946
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e340 b3e946
        have b3e5032 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e1320 X0 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1320
          | exact resolve b3e1320 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5049 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e164 X0 X1
             have i₂ := b3e1320 X0 X1
             grind)
          | exact superpose b3e1320 b3e164
          | (have j1 := b3e1320 X0 X1
             grind)
          | exact resolve b3e164 b3e1320
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1320
        have b3e5120 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e5032 (τ X0) (τ X1)
             have i₂ := b3e286 X0 X1
             grind)
          | exact superpose b3e286 b3e5032
          | exact resolve b3e5032 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5140 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e29 X1 X0
             have i₂ := b3e5032 (τ X1) X0
             grind)
          | exact superpose b3e5032 b3e29
          | (have j1 := b3e5032 (τ X1) X0
             grind)
          | exact resolve b3e29 b3e5032
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e5218 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e960 (M.op X0 X1)
             have i₂ := b3e404 X0 X1 X1
             grind)
          | exact superpose b3e404 b3e960
          | (have j0 := b3e960 (M.op X0 X1)
             grind)
          | exact resolve b3e960 b3e404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5221 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
          first
          | (have i₁ := b3e960 x
             have i₂ := b3e91
             grind)
          | exact superpose b3e91 b3e960
          | (have j0 := b3e960 x
             grind)
          | exact resolve b3e960 b3e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e960
        have b3e5228 : (τ x) = (M.op (τ x) (τ x)) := by grind
        clear b3e5221
        have b3e5229 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have j0 := b3e5218 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5218
        have b3e5283 : ∀ X0 : G, (τ x) ≠ (M.op X0 (τ x)) ∨ (τ x) = (k (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e108 X0 (τ x) (τ x)
             have i₂ := b3e5228
             grind)
          | exact superpose b3e5228 b3e108
          | exact resolve b3e108 b3e5228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5289 : ∀ X0 : G, (τ x) = (k (τ x) (M.op (τ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e404 (τ x) (τ x) x
             have i₂ := b3e5228
             grind)
          | exact superpose b3e5228 b3e404
          | exact resolve b3e404 b3e5228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e404
        have b3e5413 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (k (τ X0) y)) ∨ (σ (k (τ X0) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e1265 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1265
          | exact resolve b3e1265 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5530 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ y)) ∨ (σ (k (τ X0) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e5413 X0
             have i₂ := b3e28 X0 y
             grind)
          | exact superpose b3e28 b3e5413
          | (have j0 := b3e5413 X0
             grind)
          | exact resolve b3e5413 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5413
        have b3e5536 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e5530 X0
             have i₂ := b3e28 X0 y
             grind)
          | exact superpose b3e28 b3e5530
          | (have j0 := b3e5530 X0
             grind)
          | exact resolve b3e5530 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5530
        have b3e5577 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1279 (τ X1) (τ X0) X2
             have i₂ := b3e286 X0 X1
             grind)
          | exact superpose b3e286 b3e1279
          | exact resolve b3e1279 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1279
        have b3e5680 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e5577 X0 X1 X2
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e5577
          | (have j0 := b3e5577 X0 X1 X2
             grind)
          | exact resolve b3e5577 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5577
        have b3e5681 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e5680 X0 X1 X2
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e5680
          | (have j0 := b3e5680 X0 X1 X2
             grind)
          | exact resolve b3e5680 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5680
        have b3e5682 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X2 X1) = (M.op X2 (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e5681 X0 X1 X2
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e5681
          | (have j0 := b3e5681 X0 X1 X2
             grind)
          | exact resolve b3e5681 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5681
        have b3e5683 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e5682 X0 X1 X2
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e5682
          | (have j0 := b3e5682 X0 X1 X2
             grind)
          | exact resolve b3e5682 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5682
        have b3e5693 : ∀ X0 : G, (k x (σ (M.op (τ x) X0))) = (σ (τ x)) := by
          intro X0
          first
          | (have i₁ := b3e28 x (M.op (τ x) X0)
             have i₂ := b3e5289 X0
             grind)
          | exact superpose b3e5289 b3e28
          | exact resolve b3e28 b3e5289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5289
        have b3e5712 : ∀ X0 : G, x = (k x (σ (M.op (τ x) X0))) := by
          intro X0
          first
          | (have i₁ := b3e5693 X0
             have i₂ := b3e14 x
             grind)
          | exact superpose b3e14 b3e5693
          | exact resolve b3e5693 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5693
        have b3e10105 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ X0) y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e164 X0 y
             have i₂ := b3e5536 X0
             grind)
          | exact superpose b3e5536 b3e164
          | (have j1 := b3e5536 X0
             grind)
          | exact resolve b3e164 b3e5536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5536
        have b3e10454 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X1))) = (k (M.op X0 X1) (τ (M.op X2 (σ (M.op X0 X1))))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e187 (M.op X0 X1) (M.op X2 (σ (M.op X0 X1)))
             have i₂ := b3e3086 X0 X1 X2
             grind)
          | exact superpose b3e3086 b3e187
          | exact resolve b3e187 b3e3086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3086
        have b3e10472 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (τ (M.op X2 (σ (M.op X0 X1))))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e10454 X0 X1 X2
             have i₂ := b3e13 (M.op X0 X1)
             grind)
          | exact superpose b3e13 b3e10454
          | exact resolve b3e10454 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10454
        have b3e10501 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ (k X0 X1))) (M.op X2 (σ (τ X1)))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1291 (τ X1) (τ X0) X2
             have i₂ := b3e286 X0 X1
             grind)
          | exact superpose b3e286 b3e1291
          | exact resolve b3e1291 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1291
        have b3e10640 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ (k X0 X1))) (M.op X2 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e10501 X0 X1 X2
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e10501
          | (have j0 := b3e10501 X0 X1 X2
             grind)
          | exact resolve b3e10501 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10501
        have b3e10659 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (k X0 X1) (M.op X2 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e10640 X0 X1 X2
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e10640
          | (have j0 := b3e10640 X0 X1 X2
             grind)
          | exact resolve b3e10640 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10640
        have b3e10661 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) = (k (k X0 X1) (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e10659 X0 X1 X2
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e10659
          | (have j0 := b3e10659 X0 X1 X2
             grind)
          | exact resolve b3e10659 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10659
        have b3e10662 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (k X0 X1) (M.op X2 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e10661 X0 X1 X2
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e10661
          | (have j0 := b3e10661 X0 X1 X2
             grind)
          | exact resolve b3e10661 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10661
        have b3e12984 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1986 X0 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1986
          | exact resolve b3e1986 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e13261 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e203
             have i₂ := b3e1986 X0 (σ x) x
             grind)
          | (have i₁ := b3e203
             have i₂ := b3e1986 (σ x) (σ x) x
             grind)
          | exact superpose b3e1986 b3e203
          | (have j1 := b3e1986 X0 x x
             grind)
          | exact resolve b3e203 b3e1986
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1986
        have b3e13783 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e5049 X0 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e5049
          | exact resolve b3e5049 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e13833 : (τ (M.op x (σ x))) = (k (τ y) y) ∨ y = (k y (σ y)) := by
          first
          | (have i₁ := b3e5049 y y
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e5049
          | (have j0 := b3e5049 y y
             grind)
          | exact resolve b3e5049 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e13834 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ y) X0) ∨ y = (k y (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e5049 y X0
             have i₂ := b3e67 (σ X0)
             grind)
          | exact superpose b3e67 b3e5049
          | (have j0 := b3e5049 y X0
             grind)
          | exact resolve b3e5049 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e13934 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e13783 X0 X1
             have i₂ := b3e286 X0 X1
             grind)
          | exact superpose b3e286 b3e13783
          | (have j0 := b3e13783 X0 X1
             grind)
          | exact resolve b3e13783 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13783
        have b3e14095 : ∀ X0 X1 X2 : G, (τ (k X2 (k X0 X1))) = (k (τ X2) (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e286 (k X0 X1) X2
             have i₂ := b3e13934 X1 X0
             grind)
          | exact superpose b3e13934 b3e286
          | (have j1 := b3e13934 X1 X0
             grind)
          | exact resolve b3e286 b3e13934
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13934
        have b3e14153 : ∀ X0 X1 X2 : G, (τ (k X2 (k X0 X1))) = (τ (k X2 (M.op X0 X1))) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e14095 X0 X1 X2
             have i₂ := b3e286 (M.op X0 X1) X2
             grind)
          | exact superpose b3e286 b3e14095
          | (have j0 := b3e14095 X0 X1 X2
             grind)
          | exact resolve b3e14095 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14095
        have b3e14434 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) X2) = (M.op (σ (τ X1)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1936 (τ X0) (τ X1) X2
             have i₂ := b3e286 X1 X0
             grind)
          | exact superpose b3e286 b3e1936
          | (have j0 := b3e1936 (τ X0) (τ X1) X2
             grind)
          | exact resolve b3e1936 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e14558 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) X2) = (M.op (σ (τ X1)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e14434 X0 X1 X2
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e14434
          | (have j0 := b3e14434 X0 X1 X2
             grind)
          | exact resolve b3e14434 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14434
        have b3e14598 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X0)) X2) = (M.op (σ (τ X1)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e14558 X0 X1 X2
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e14558
          | (have j0 := b3e14558 X0 X1 X2
             grind)
          | exact resolve b3e14558 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14558
        have b3e14626 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (σ (τ X0)) X2) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e14598 X0 X1 X2
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e14598
          | (have j0 := b3e14598 X0 X1 X2
             grind)
          | exact resolve b3e14598 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14598
        have b3e14645 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e14626 X0 X1 X2
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e14626
          | (have j0 := b3e14626 X0 X1 X2
             grind)
          | exact resolve b3e14626 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14626
        have b3e14657 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e14645 X0 X1 X2
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e14645
          | (have j0 := b3e14645 X0 X1 X2
             grind)
          | exact resolve b3e14645 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14645
        have b3e14662 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e14657 X0 X1 X2
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e14657
          | (have j0 := b3e14657 X0 X1 X2
             grind)
          | exact resolve b3e14657 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14657
        have b3e16897 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e95 (σ y)
             have i₂ := b3e451 y
             grind)
          | exact superpose b3e451 b3e95
          | (have j1 := b3e451 y
             grind)
          | exact resolve b3e95 b3e451
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e451
        have b3e16940 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b3e16897
        have b3e17757 : ∀ X0 X1 X2 : G, (τ (σ (M.op (τ (σ X0)) X1))) = (k X0 (τ (σ (M.op X2 X1)))) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e187 X0 (σ (M.op X2 X1))
             have i₂ := b3e1480 (σ X0) X1 X2
             grind)
          | exact superpose b3e1480 b3e187
          | (have j1 := b3e1480 (σ X0) X1 X2
             grind)
          | exact resolve b3e187 b3e1480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e187 b3e1480
        have b3e17811 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X1)) = (τ (σ (M.op (τ (σ X0)) X1))) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e17757 X0 X1 X2
             have i₂ := b3e13 (M.op X2 X1)
             grind)
          | exact superpose b3e13 b3e17757
          | (have j0 := b3e17757 X0 X1 X2
             grind)
          | exact resolve b3e17757 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17757
        have b3e17854 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X1)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e17811 X0 X1 X2
             have i₂ := b3e13 (M.op (τ (σ X0)) X1)
             grind)
          | exact superpose b3e13 b3e17811
          | (have j0 := b3e17811 X0 X1 X2
             grind)
          | exact resolve b3e17811 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17811
        have b3e17887 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e17854 X0 X1 X2
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e17854
          | (have j0 := b3e17854 X0 X1 X2
             grind)
          | exact resolve b3e17854 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17854
        have b3e17907 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e17887 X0 X1 X2
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e17887
          | (have j0 := b3e17887 X0 X1 X2
             grind)
          | exact resolve b3e17887 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17887
        have b3e17917 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e17907 X0 X1 X2
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e17907
          | (have j0 := b3e17907 X0 X1 X2
             grind)
          | exact resolve b3e17907 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17907
        have b3e18706 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e5140 X0 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e5140
          | exact resolve b3e5140 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5140
        have b3e18848 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e18706 X0 X1
             have i₂ := b3e18 X1 X0
             grind)
          | exact superpose b3e18 b3e18706
          | (have j0 := b3e18706 X0 X1
             grind)
          | exact resolve b3e18706 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18706
        have b3e22871 : ∀ X0 : G, x = (k x (k (τ X0) y)) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e771 X0
             have i₂ := b3e10105 X0
             grind)
          | exact superpose b3e10105 b3e771
          | (have j1 := b3e10105 X0
             grind)
          | exact resolve b3e771 b3e10105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10105
        have b3e23072 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) X1) ∨ (M.op X0 (σ x)) = (σ (k (τ X0) y)) ∨ (M.op X0 (σ x)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1760 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1760
          | exact resolve b3e1760 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1760
        have b3e23615 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (k X0 (σ y)) ∨ (M.op X0 X1) = (M.op (σ y) X1) ∨ (M.op X0 (σ x)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e23072 X0 X1
             have i₂ := b3e28 X0 y
             grind)
          | exact superpose b3e28 b3e23072
          | (have j0 := b3e23072 X0 X1
             grind)
          | exact resolve b3e23072 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23072
        have b3e24855 : ∀ X0 : G, (τ (M.op x X0)) = (k (τ y) (τ X0)) ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e13834 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e13834
          | exact resolve b3e13834 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24977 : ∀ X0 : G, (τ (M.op x X0)) = (τ (k y X0)) ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e24855 X0
             have i₂ := b3e286 X0 y
             grind)
          | exact superpose b3e286 b3e24855
          | (have j0 := b3e24855 X0
             grind)
          | exact resolve b3e24855 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24855
        have b3e25239 : ∀ X0 : G, (k y X0) = (σ (τ (M.op x X0))) ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e14 (k y X0)
             have i₂ := b3e24977 X0
             grind)
          | exact superpose b3e24977 b3e14
          | (have j1 := b3e24977 X0
             grind)
          | exact resolve b3e14 b3e24977
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24977
        have b3e25322 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e25239 X0
             have i₂ := b3e14 (M.op x X0)
             grind)
          | exact superpose b3e14 b3e25239
          | (have j0 := b3e25239 X0
             grind)
          | exact resolve b3e25239 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25239
        have b3e29497 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1937 (τ X1) (τ X0)
             have i₂ := b3e286 X0 X1
             grind)
          | exact superpose b3e286 b3e1937
          | (have j0 := b3e1937 (τ X0) (τ X1)
             grind)
          | exact resolve b3e1937 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1937
        have b3e29692 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e29497 X0 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e29497
          | (have j0 := b3e29497 X0 X1
             grind)
          | exact resolve b3e29497 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29497
        have b3e29741 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e29692 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e29692
          | (have j0 := b3e29692 X0 X1
             grind)
          | exact resolve b3e29692 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29692
        have b3e29775 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e29741 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e29741
          | (have j0 := b3e29741 X0 X1
             grind)
          | exact resolve b3e29741 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29741
        have b3e29792 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e29775 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e29775
          | (have j0 := b3e29775 X0 X1
             grind)
          | exact resolve b3e29775 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29775
        have b3e29803 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e29792 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e29792
          | (have j0 := b3e29792 X0 X1
             grind)
          | exact resolve b3e29792 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29792
        have b3e29810 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e29803 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e29803
          | (have j0 := b3e29803 X0 X1
             grind)
          | exact resolve b3e29803 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29803
        have b3e29813 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e29810 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e29810
          | (have j0 := b3e29810 X0 X1
             grind)
          | exact resolve b3e29810 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29810
        have b3e31007 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (k (k X0 (τ X1)) X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e1101 (σ X0) X1
             have i₂ := b3e911 X0 X1 X0
             grind)
          | exact superpose b3e911 b3e1101
          | (have j1 := b3e911 X0 X1 x
             grind)
          | exact resolve b3e1101 b3e911
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e911 b3e1101
        have b3e89320 : (k (τ (σ y)) x) = (τ (σ (k y y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e5049 (σ y) x
             have i₂ := b3e16940
             grind)
          | exact superpose b3e16940 b3e5049
          | (have j0 := b3e5049 (σ y) x
             grind)
          | exact resolve b3e5049 b3e16940
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e16940
        have b3e89409 : (k (τ (σ y)) x) = (τ (σ (k y y))) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have j1 := b3e15 (σ y) (σ x)
             grind)
          | (have r₁ := b3e89320
             have r₂ := b3e15 (σ y) (σ x)
             grind)
          | exact resolve b3e89320 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89320
        have b3e89482 : (k y y) = (k (τ (σ y)) x) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e89409
             have i₂ := b3e13 (k y y)
             grind)
          | exact superpose b3e13 b3e89409
          | exact resolve b3e89409 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89409
        have b3e89516 : (k y x) = (k y y) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e89482
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e89482
          | exact resolve b3e89482 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89482
        have b3e89529 : (σ y) = (σ (k y x)) ∨ (k y x) = (k y y) := by
          first
          | (have i₁ := b3e89516
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e89516
          | exact resolve b3e89516 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89516
        have b3e90158 : (k y x) = (τ (σ y)) ∨ (k y x) = (k y y) := by
          first
          | (have i₁ := b3e13 (k y x)
             have i₂ := b3e89529
             grind)
          | exact superpose b3e89529 b3e13
          | exact resolve b3e13 b3e89529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89529
        have b3e90465 : (k y x) = (k y y) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e90158
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e90158
          | exact resolve b3e90158 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90158
        have b3e91034 : (M.op x y) = (k y x) ∨ y = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e25322 y
             have i₂ := b3e90465
             grind)
          | exact superpose b3e90465 b3e25322
          | (have j0 := b3e25322 x
             grind)
          | exact resolve b3e25322 b3e90465
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25322 b3e90465
        have b3e91152 : (M.op x y) = (k y x) ∨ y = (k y x) := by grind
        clear b3e91034
        have b3e91716 : (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b3e91152
             have i₂ := b3e17 y x
             grind)
          | exact superpose b3e17 b3e91152
          | (have j1 := b3e17 y x
             grind)
          | exact resolve b3e91152 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e91803 : (σ (M.op x y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e18848 x y
             have i₂ := b3e91152
             grind)
          | exact superpose b3e91152 b3e18848
          | (have j0 := b3e18848 x y
             grind)
          | exact resolve b3e18848 b3e91152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18848
        have b3e91810 : y ≠ (M.op x y) ∨ y = (k y x) := by grind
        clear b3e91152
        have b3e91811 : (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
        clear b3e91716
        have b3e91814 : (σ (M.op x y)) = (σ (M.op y x)) ∨ y = (k y x) := by
          first
          | (have r₁ := b3e91803
             have r₂ := b3e91810
             grind)
          | exact resolve b3e91803 b3e91810
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91803 b3e91810
        have b3e91847 : x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e91811
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e91811
          | exact resolve b3e91811 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91811
        have b3e91850 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e91814
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e91814
          | exact resolve b3e91814 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91814
        have b3e91862 : y = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b3e91847
             have r₂ := b3e20
             grind)
          | exact resolve b3e91847 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91847
        have b3e91865 : y = (k y x) := by
          first
          | (have r₁ := b3e91850
             have r₂ := b3e23
             grind)
          | exact resolve b3e91850 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91850
        have b3e91871 : y = (M.op x y) ∨ x = y := by
          first
          | (have i₁ := b3e91862
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e91862
          | exact resolve b3e91862 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91862
        have b3e92910 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e492 y x
             have i₂ := b3e91865
             grind)
          | exact superpose b3e91865 b3e492
          | (have j0 := b3e492 y x
             grind)
          | exact resolve b3e492 b3e91865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e492
        have b3e92931 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e1936 y x X0
             have i₂ := b3e91865
             grind)
          | exact superpose b3e91865 b3e1936
          | (have j0 := b3e1936 x y X0
             grind)
          | exact resolve b3e1936 b3e91865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1936 b3e91865
        have b3e92938 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have j0 := b3e92931 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92931
        have b3e92941 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b3e92910
        have b3e92953 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e92941
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e92941
          | exact resolve b3e92941 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92941
        have b3e93281 : (τ y) = (M.op (τ y) (τ y)) ∨ x = y := by
          first
          | (have i₁ := b3e5229 x y
             have i₂ := b3e91871
             grind)
          | exact superpose b3e91871 b3e5229
          | exact resolve b3e5229 b3e91871
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5229 b3e91871
        have b3e98382 : (τ y) = (τ (k y y)) ∨ (τ y) = (τ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b3e5120 y y
             have i₂ := b3e93281
             grind)
          | exact superpose b3e93281 b3e5120
          | (have j0 := b3e5120 y y
             grind)
          | exact resolve b3e5120 b3e93281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5120 b3e93281
        have b3e98452 : (τ y) = (τ (k y y)) ∨ x = y := by grind
        clear b3e98382
        have b3e99130 : ∀ X0 : G, (k (τ X0) (τ y)) = (τ (k X0 (k y y))) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b3e286 (k y y) X0
             have i₂ := b3e98452
             grind)
          | exact superpose b3e98452 b3e286
          | exact resolve b3e286 b3e98452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98452
        have b3e99262 : ∀ X0 : G, (τ (k X0 y)) = (τ (k X0 (k y y))) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b3e99130 X0
             have i₂ := b3e286 y X0
             grind)
          | exact superpose b3e286 b3e99130
          | exact resolve b3e99130 b3e286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e286 b3e99130
        have b3e112586 : (σ y) = (σ (k y y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1265 y
             have i₂ := b3e92953
             grind)
          | exact superpose b3e92953 b3e1265
          | (have j0 := b3e1265 y
             grind)
          | exact resolve b3e1265 b3e92953
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1265
        have b3e112754 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b3e112586
        have b3e138721 : ∀ X0 : G, (k X0 (k y y)) = (σ (τ (k X0 y))) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b3e14 (k X0 (k y y))
             have i₂ := b3e99262 X0
             grind)
          | exact superpose b3e99262 b3e14
          | exact resolve b3e14 b3e99262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99262
        have b3e138872 : ∀ X0 : G, (k X0 y) = (k X0 (k y y)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b3e138721 X0
             have i₂ := b3e14 (k X0 y)
             grind)
          | exact superpose b3e14 b3e138721
          | exact resolve b3e138721 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e138721
        have b3e141446 : ∀ X0 : G, (k X0 y) = (M.op X0 (k y y)) ∨ (k X0 y) = X0 ∨ x = y := by
          intro X0
          first
          | (have i₁ := b3e5032 (k y y) X0
             have i₂ := b3e138872 X0
             grind)
          | exact superpose b3e138872 b3e5032
          | (have j0 := b3e5032 y X0
             grind)
          | exact resolve b3e5032 b3e138872
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5032 b3e138872
        have b3e320334 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e209 (σ y)
             have i₂ := b3e92938 (σ x)
             grind)
          | exact superpose b3e92938 b3e209
          | (have j0 := b3e209 (σ x)
             grind)
          | (have r₁ := b3e209 (σ y)
             have r₂ := b3e92938 x
             grind)
          | exact resolve b3e209 b3e92938
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e320463 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b3e92938
        have b3e320476 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e320463
             have i₂ := b3e203
             grind)
          | exact superpose b3e203 b3e320463
          | exact resolve b3e320463 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e320463
        have b3e320527 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have j1 := b3e209 (σ x)
             grind)
          | (have r₁ := b3e320334
             have r₂ := b3e209 (σ y)
             grind)
          | exact resolve b3e320334 b3e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209 b3e320334
        have b3e320543 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b3e320476
             have r₂ := b3e92953
             grind)
          | exact resolve b3e320476 b3e92953
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92953 b3e320476
        have b3e320553 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e320527
             have i₂ := b3e203
             grind)
          | exact superpose b3e203 b3e320527
          | exact resolve b3e320527 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e203 b3e320527
        have b3e320565 : (σ y) = (σ (k y y)) ∨ (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e320553
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e320553
          | exact resolve b3e320553 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e320553
        have b3e320569 : (σ y) = (σ (k y y)) := by
          first
          | (have r₁ := b3e320565
             have r₂ := b3e112754
             grind)
          | exact resolve b3e320565 b3e112754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e112754 b3e320565
        have b3e321155 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e539 y y x
             have i₂ := b3e320569
             grind)
          | exact superpose b3e320569 b3e539
          | (have j0 := b3e539 y y x
             grind)
          | exact resolve b3e539 b3e320569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e539
        have b3e321166 : (τ (σ y)) = (k y y) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e320569
             grind)
          | exact superpose b3e320569 b3e13
          | exact resolve b3e13 b3e320569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e321276 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b3e321155 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321155
        have b3e321329 : y = (k y y) := by
          first
          | (have i₁ := b3e321166
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e321166
          | exact resolve b3e321166 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321166
        have b3e321332 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have j0 := b3e321276 X0
             have j1 := b3e101 (σ y) (σ y) X0
             grind)
          | (have r₁ := b3e321276 X0
             have r₂ := b3e101 (σ y) (σ y) x
             grind)
          | exact resolve b3e321276 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101 b3e321276
        have b3e321351 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e321332 X0
             have i₂ := b3e95 X0
             grind)
          | exact superpose b3e95 b3e321332
          | exact resolve b3e321332 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321332
        have b3e322033 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e1433 y y
             have i₂ := b3e321329
             grind)
          | exact superpose b3e321329 b3e1433
          | (have j0 := b3e1433 y y
             grind)
          | (have r₁ := b3e1433 y y
             have r₂ := b3e321329
             grind)
          | exact resolve b3e1433 b3e321329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1433
        have b3e322042 : y ≠ y ∨ y = (M.op y y) := by grind
        clear b3e322033
        have b3e322043 : y = (M.op y y) := by grind
        clear b3e322042
        have b3e322063 : y = (M.op x y) := by
          first
          | (have i₁ := b3e322043
             have i₂ := b3e67 y
             grind)
          | exact superpose b3e67 b3e322043
          | exact resolve b3e322043 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e322043
        have b3e322649 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e322063
             grind)
          | exact superpose b3e322063 b3e20
          | exact resolve b3e20 b3e322063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e322650 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e322063
             grind)
          | exact superpose b3e322063 b3e23
          | exact resolve b3e23 b3e322063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e322731 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 y) x) := by
          intro X0
          first
          | (have i₁ := b3e108 x y X0
             have i₂ := b3e322063
             grind)
          | exact superpose b3e322063 b3e108
          | (have j0 := b3e108 x y X0
             grind)
          | exact resolve b3e108 b3e322063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e108
        have b3e322767 : ∀ X0 : G, y = (k y (τ (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b3e10472 x y x
             have i₂ := b3e322063
             grind)
          | exact superpose b3e322063 b3e10472
          | exact resolve b3e10472 b3e322063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10472
        have b3e322789 : ∀ X0 : G, y = (k y (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e322767 X0
             have i₂ := b3e95 X0
             grind)
          | exact superpose b3e95 b3e322767
          | exact resolve b3e322767 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e322767
        have b3e506045 : ∀ X0 X1 : G, (k (M.op X0 X1) y) = (M.op X0 (k y y)) ∨ (M.op X0 X1) = (k (M.op X0 X1) y) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b3e44 X0 X1 (k y y)
             have i₂ := b3e141446 (M.op X0 X1)
             grind)
          | exact superpose b3e141446 b3e44
          | (have j1 := b3e141446 (M.op X0 X1)
             grind)
          | exact resolve b3e44 b3e141446
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141446
        have b3e506281 : ∀ X0 X1 : G, (k (M.op X0 X1) y) = (M.op X0 (k y y)) ∨ (M.op X0 X1) = (k (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have j0 := b3e506045 X0 X1
             grind)
          | (have r₁ := b3e506045 X0 X1
             have r₂ := b3e322649
             grind)
          | exact resolve b3e506045 b3e322649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e506045
        have b3e506370 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X0 X1) y) ∨ (M.op X0 X1) = (k (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e506281 X0 X1
             have i₂ := b3e321329
             grind)
          | exact superpose b3e321329 b3e506281
          | (have j0 := b3e506281 X0 X1
             grind)
          | exact resolve b3e506281 b3e321329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321329 b3e506281
        have b3e636784 : ∀ X0 X1 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X1) = (M.op x X1) ∨ (M.op X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e67 X1
             have i₂ := b3e12984 y X0 X1
             grind)
          | (have i₁ := b3e67 x
             have i₂ := b3e12984 X0 y x
             grind)
          | exact superpose b3e12984 b3e67
          | (have j1 := b3e12984 y X0 x
             grind)
          | exact resolve b3e67 b3e12984
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12984
        have b3e656415 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (σ (τ (k X0 (M.op X1 X2)))) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e14 (k X0 (k X1 X2))
             have i₂ := b3e14153 X1 X2 X0
             grind)
          | exact superpose b3e14153 b3e14
          | (have j1 := b3e14153 X1 X2 X2
             grind)
          | exact resolve b3e14 b3e14153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14153
        have b3e656461 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X1 X2)) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e656415 X0 X1 X2
             have i₂ := b3e14 (k X0 (M.op X1 X2))
             grind)
          | exact superpose b3e14 b3e656415
          | (have j0 := b3e656415 X0 X1 X2
             grind)
          | exact resolve b3e656415 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e656415
        have b3e657080 : ∀ X0 X1 : G, (k X0 X1) ≠ (k (k X0 X1) (M.op X0 X1)) ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e952 (k X0 X1)
             have i₂ := b3e656461 (k X0 X1) X0 X1
             grind)
          | exact superpose b3e656461 b3e952
          | (have j0 := b3e952 (k X0 X1)
             have j1 := b3e656461 X0 X0 X1
             grind)
          | (have r₁ := b3e952 x
             have r₂ := b3e656461 X0 x x
             grind)
          | exact resolve b3e952 b3e656461
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e952 b3e656461
        have b3e657528 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e657080 X0 X1
             have j1 := b3e10662 X0 X1 x
             grind)
          | (have r₁ := b3e657080 x X1
             have r₂ := b3e10662 x X1 x
             grind)
          | (have r₁ := b3e657080 X0 X1
             have r₂ := b3e10662 (k X0 X1) (M.op X0 X1) x
             grind)
          | exact resolve b3e657080 b3e10662
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10662 b3e657080
        have b3e658018 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e5683 X0 X1 (k X0 X1)
             have i₂ := b3e657528 X0 X1
             grind)
          | exact superpose b3e657528 b3e5683
          | (have j0 := b3e5683 X0 X1 x
             have j1 := b3e657528 X0 X1
             grind)
          | exact resolve b3e5683 b3e657528
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5683 b3e657528
        have b3e658096 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e658018 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e658018
        have b3e805882 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have j0 := b3e506370 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e506370
        have b3e806046 : (τ x) ≠ (M.op (τ x) y) ∨ (k (τ x) y) = (M.op (τ x) y) := by
          first
          | (have i₁ := b3e805882 (τ x) (τ x)
             have i₂ := b3e5228
             grind)
          | exact superpose b3e5228 b3e805882
          | exact resolve b3e805882 b3e5228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e885573 : ∀ X0 : G, x = (k x (σ (M.op x X0))) ∨ (k (τ x) y) = (M.op (τ x) y) ∨ (τ x) = (M.op (τ x) y) := by
          intro X0
          first
          | (have i₁ := b3e5712 X0
             have i₂ := b3e636784 (τ x) X0
             grind)
          | exact superpose b3e636784 b3e5712
          | (have j1 := b3e636784 (τ x) x
             grind)
          | exact resolve b3e5712 b3e636784
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5712
        have b3e885609 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op x x) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e39 x X1
             have i₂ := b3e636784 X0 X1
             grind)
          | (have i₁ := b3e39 X0 X1
             have i₂ := b3e636784 X0 X1
             grind)
          | exact superpose b3e636784 b3e39
          | (have j1 := b3e636784 X0 X1
             grind)
          | exact resolve b3e39 b3e636784
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e636784
        have b3e885737 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) x) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e885609 X0 X1
             have i₂ := b3e62
             grind)
          | exact superpose b3e62 b3e885609
          | (have j0 := b3e885609 X0 X1
             grind)
          | exact resolve b3e885609 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e885609
        have b3e885752 : ∀ X0 : G, x = (k x (σ (M.op x X0))) ∨ (k (τ x) y) = (M.op (τ x) y) := by
          intro X0
          first
          | (have j0 := b3e885573 X0
             grind)
          | (have r₁ := b3e885573 X0
             have r₂ := b3e806046
             grind)
          | exact resolve b3e885573 b3e806046
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e806046 b3e885573
        have b3e885789 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ x = (M.op X0 x) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e885737 X0 x
             have i₂ := b3e39 X0 x
             grind)
          | exact superpose b3e39 b3e885737
          | (have j0 := b3e885737 X0 x
             grind)
          | exact resolve b3e885737 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e885737
        have b3e888512 : (k (τ x) y) = (M.op (τ x) y) ∨ x = (k x (σ y)) := by
          first
          | (have i₁ := b3e885752 y
             have i₂ := b3e322063
             grind)
          | exact superpose b3e322063 b3e885752
          | exact resolve b3e885752 b3e322063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e322063 b3e885752
        have b3e888804 : x = (k x (M.op (τ x) y)) ∨ x = (k x (σ y)) ∨ x = (k x (σ y)) := by
          first
          | (have i₁ := b3e22871 x
             have i₂ := b3e888512
             grind)
          | exact superpose b3e888512 b3e22871
          | (have j0 := b3e22871 x
             grind)
          | exact resolve b3e22871 b3e888512
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22871 b3e888512
        have b3e888962 : x = (k x (M.op (τ x) y)) ∨ x = (k x (σ y)) := by grind
        clear b3e888804
        have b3e889056 : x = (M.op x y) ∨ x = (M.op (τ x) x) ∨ x = (M.op x y) ∨ x = (k x (σ y)) := by
          first
          | (have i₁ := b3e17917 x y (τ x)
             have i₂ := b3e888962
             grind)
          | exact superpose b3e888962 b3e17917
          | (have j0 := b3e17917 x y (τ x)
             grind)
          | exact resolve b3e17917 b3e888962
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e888962
        have b3e889059 : x = (M.op x y) ∨ x = (M.op (τ x) x) ∨ x = (k x (σ y)) := by grind
        clear b3e889056
        have b3e889062 : x = (k x (σ y)) ∨ x = (M.op (τ x) x) := by
          first
          | (have r₁ := b3e889059
             have r₂ := b3e20
             grind)
          | exact resolve b3e889059 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e889059
        have b3e889091 : (τ x) = (k (τ x) y) ∨ x = (M.op (τ x) x) := by
          first
          | (have i₁ := b3e164 x y
             have i₂ := b3e889062
             grind)
          | exact superpose b3e889062 b3e164
          | exact resolve b3e164 b3e889062
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e889062
        have b3e889218 : (τ x) = (M.op (τ x) y) ∨ x = (M.op (τ x) x) ∨ (τ x) = (M.op (τ x) y) ∨ x = (M.op (τ x) x) := by
          first
          | (have i₁ := b3e885789 (τ x)
             have i₂ := b3e889091
             grind)
          | exact superpose b3e889091 b3e885789
          | (have j0 := b3e885789 (τ x)
             grind)
          | exact resolve b3e885789 b3e889091
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e885789 b3e889091
        have b3e889225 : (τ x) = (M.op (τ x) y) ∨ x = (M.op (τ x) x) := by grind
        clear b3e889218
        have b3e889391 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ x)) ∨ x = (M.op (τ x) x) := by
          intro X0
          first
          | (have i₁ := b3e43 y X0 (τ x)
             have i₂ := b3e889225
             grind)
          | exact superpose b3e889225 b3e43
          | exact resolve b3e43 b3e889225
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e889225
        have b3e890212 : ∀ X0 X1 : G, (M.op x X0) = (M.op (τ x) X0) ∨ (M.op X1 (τ x)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e44 (τ x) x X0
             have i₂ := b3e889391 X1
             grind)
          | exact superpose b3e889391 b3e44
          | (have j1 := b3e889391 X1
             grind)
          | exact resolve b3e44 b3e889391
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e889391
        have b3e898580 : ∀ X0 : G, (τ x) = (M.op x (τ x)) ∨ (M.op X0 y) = (M.op X0 (τ x)) := by
          intro X0
          first
          | (have i₁ := b3e5228
             have i₂ := b3e890212 (τ x) X0
             grind)
          | exact superpose b3e890212 b3e5228
          | (have j1 := b3e890212 X0 X0
             grind)
          | exact resolve b3e5228 b3e890212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e890212
        have b3e900080 : (τ x) = (M.op (τ x) y) ∨ (τ x) = (M.op x (τ x)) := by
          first
          | (have i₁ := b3e5228
             have i₂ := b3e898580 (τ x)
             grind)
          | exact superpose b3e898580 b3e5228
          | exact resolve b3e5228 b3e898580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5228 b3e898580
        have b3e900578 : y ≠ (τ x) ∨ (τ x) = (k (τ x) x) ∨ (τ x) = (M.op x (τ x)) := by
          first
          | (have i₁ := b3e322731 (τ x)
             have i₂ := b3e900080
             grind)
          | exact superpose b3e900080 b3e322731
          | exact resolve b3e322731 b3e900080
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e322731
        have b3e900666 : (τ x) ≠ (τ x) ∨ (τ x) = (k (τ x) y) ∨ (τ x) = (M.op x (τ x)) := by
          first
          | (have i₁ := b3e805882 (τ x) y
             have i₂ := b3e900080
             grind)
          | exact superpose b3e900080 b3e805882
          | exact resolve b3e805882 b3e900080
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e805882 b3e900080
        have b3e900667 : (τ x) = (k (τ x) y) ∨ (τ x) = (M.op x (τ x)) := by grind
        clear b3e900666
        have b3e900674 : (τ x) = (k (τ x) y) := by
          first
          | (have j1 := b3e158 (τ x)
             grind)
          | (have r₁ := b3e900667
             have r₂ := b3e158 (τ x)
             grind)
          | exact resolve b3e900667 b3e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e158 b3e900667
        have b3e900712 : y ≠ (τ x) ∨ (τ x) = (k (τ x) x) := by
          first
          | (have j1 := b3e5283 x
             grind)
          | (have r₁ := b3e900578
             have r₂ := b3e5283 x
             grind)
          | exact resolve b3e900578 b3e5283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5283 b3e900578
        have b3e900883 : (σ (τ x)) = (k x (σ y)) := by
          first
          | (have i₁ := b3e28 x y
             have i₂ := b3e900674
             grind)
          | exact superpose b3e900674 b3e28
          | exact resolve b3e28 b3e900674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e900674
        have b3e900980 : x = (k x (σ y)) := by
          first
          | (have i₁ := b3e900883
             have i₂ := b3e14 x
             grind)
          | exact superpose b3e14 b3e900883
          | exact resolve b3e900883 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e900883
        have b3e901037 : ∀ X0 : G, x = (M.op x (σ x)) ∨ (M.op x X0) = (M.op (σ y) X0) ∨ x = (M.op x (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e23615 x X0
             have i₂ := b3e900980
             grind)
          | exact superpose b3e900980 b3e23615
          | (have j0 := b3e23615 x X0
             grind)
          | exact resolve b3e23615 b3e900980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23615 b3e900980
        have b3e901142 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) ∨ x = (M.op x (σ x)) := by
          intro X0
          first
          | (have j0 := b3e901037 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e901037
        have b3e903000 : (σ y) = (M.op x (σ x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b3e320543
             have i₂ := b3e901142 (σ x)
             grind)
          | exact superpose b3e901142 b3e320543
          | exact resolve b3e320543 b3e901142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e901142
        have b3e903731 : (k (τ x) x) = (τ (σ y)) ∨ x = (k x (σ x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b3e5049 x x
             have i₂ := b3e903000
             grind)
          | exact superpose b3e903000 b3e5049
          | (have j0 := b3e5049 x x
             grind)
          | exact resolve b3e5049 b3e903000
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5049
        have b3e903863 : (k (τ x) x) = (τ (σ y)) ∨ x = (k x (σ x)) := by
          first
          | (have j1 := b3e15 x (σ x)
             grind)
          | (have r₁ := b3e903731
             have r₂ := b3e15 x (σ x)
             grind)
          | exact resolve b3e903731 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e903731
        have b3e903966 : y = (k (τ x) x) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b3e903863
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e903863
          | exact resolve b3e903863 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e903863
        have b3e904277 : y = (M.op y x) ∨ y = (τ x) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b3e658096 (τ x) x
             have i₂ := b3e903966
             grind)
          | exact superpose b3e903966 b3e658096
          | (have j0 := b3e658096 x (σ x)
             grind)
          | exact resolve b3e658096 b3e903966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e658096 b3e903966
        have b3e904334 : x = y ∨ y = (τ x) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b3e904277
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e904277
          | exact resolve b3e904277 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e904277
        have b3e904441 : x = (k x (σ x)) ∨ y = (τ x) := by
          first
          | (have r₁ := b3e904334
             have r₂ := b3e322649
             grind)
          | exact resolve b3e904334 b3e322649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e904334
        have b3e904488 : (τ x) = (k (τ x) x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e164 x x
             have i₂ := b3e904441
             grind)
          | exact superpose b3e904441 b3e164
          | exact resolve b3e164 b3e904441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e164 b3e904441
        have b3e904529 : (τ x) = (k (τ x) x) := by
          first
          | (have r₁ := b3e904488
             have r₂ := b3e900712
             grind)
          | exact resolve b3e904488 b3e900712
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e900712 b3e904488
        have b3e904575 : (σ (τ x)) = (k x (σ x)) := by
          first
          | (have i₁ := b3e28 x x
             have i₂ := b3e904529
             grind)
          | exact superpose b3e904529 b3e28
          | exact resolve b3e28 b3e904529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e904529
        have b3e904653 : x = (k x (σ x)) := by
          first
          | (have i₁ := b3e904575
             have i₂ := b3e14 x
             grind)
          | exact superpose b3e14 b3e904575
          | exact resolve b3e904575 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e904575
        have b3e904702 : x = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b3e13261 x
             have i₂ := b3e904653
             grind)
          | exact superpose b3e904653 b3e13261
          | (have j0 := b3e13261 x
             grind)
          | exact resolve b3e13261 b3e904653
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e904653
        have b3e904807 : (σ x) = (M.op x (σ x)) ∨ x = (M.op x (σ x)) := by grind
        clear b3e904702
        have b3e905776 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b3e903000
             have i₂ := b3e904807
             grind)
          | exact superpose b3e904807 b3e903000
          | exact resolve b3e903000 b3e904807
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e903000
        have b3e905997 : x ≠ (σ x) ∨ x = (M.op x (σ x)) := by grind
        clear b3e904807
        have b3e906117 : (σ x) = (σ y) ∨ x = (M.op x (σ x)) := by
          first
          | (have r₁ := b3e905776
             have r₂ := b3e905997
             grind)
          | exact resolve b3e905776 b3e905997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e905776 b3e905997
        have b3e906170 : x = (M.op x (σ x)) := by
          first
          | (have r₁ := b3e906117
             have r₂ := b3e322650
             grind)
          | exact resolve b3e906117 b3e322650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e906117
        have b3e906197 : (τ x) = (k (τ y) y) ∨ y = (k y (σ y)) := by
          first
          | (have i₁ := b3e13833
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e13833
          | exact resolve b3e13833 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13833
        have b3e906208 : (τ x) = (k (τ y) x) ∨ y = (k y (σ x)) := by
          first
          | (have i₁ := b3e13834 x
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e13834
          | (have j0 := b3e13834 x
             grind)
          | exact resolve b3e13834 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13834
        have b3e906308 : (σ x) = (k (σ x) x) := by
          first
          | (have i₁ := b3e536 x
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e536
          | exact resolve b3e536 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e536
        have b3e906311 : x = (k x (τ x)) := by
          first
          | (have i₁ := b3e771 x
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e771
          | exact resolve b3e771 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e771
        have b3e906335 : (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b3e321351 x
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e321351
          | exact resolve b3e321351 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321351
        have b3e906336 : y = (k y (τ x)) := by
          first
          | (have i₁ := b3e322789 x
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e322789
          | exact resolve b3e322789 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e322789
        have b3e906744 : (M.op (σ x) x) = (σ (k x x)) ∨ (σ x) = (M.op x (σ x)) ∨ (σ x) = (M.op (σ x) x) := by
          first
          | (have i₁ := b3e31007 x x
             have i₂ := b3e906311
             grind)
          | exact superpose b3e906311 b3e31007
          | (have j0 := b3e31007 x x
             grind)
          | exact resolve b3e31007 b3e906311
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e906311
        have b3e906797 : (σ x) = (M.op (σ x) x) ∨ (σ x) = (M.op x (σ x)) ∨ (σ x) = (M.op (σ x) x) := by
          first
          | (have i₁ := b3e906744
             have i₂ := b3e91
             grind)
          | exact superpose b3e91 b3e906744
          | exact resolve b3e906744 b3e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91 b3e906744
        have b3e906798 : (σ x) = (M.op (σ x) x) ∨ (σ x) = (M.op x (σ x)) := by grind
        clear b3e906797
        have b3e906816 : (σ x) = (M.op (σ x) x) ∨ x = (σ x) := by
          first
          | (have i₁ := b3e906798
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e906798
          | exact resolve b3e906798 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e906798
        have b3e906882 : (σ (k y y)) = (M.op (σ y) x) ∨ (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b3e31007 y x
             have i₂ := b3e906336
             grind)
          | exact superpose b3e906336 b3e31007
          | (have j0 := b3e31007 y x
             grind)
          | exact resolve b3e31007 b3e906336
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31007 b3e906336
        have b3e906964 : (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b3e906882
             have i₂ := b3e320569
             grind)
          | exact superpose b3e320569 b3e906882
          | exact resolve b3e906882 b3e320569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e320569 b3e906882
        have b3e906965 : (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op x (σ y)) := by grind
        clear b3e906964
        have b3e907005 : (σ y) = (M.op x (σ x)) ∨ (σ y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b3e906965
             have i₂ := b3e95 x
             grind)
          | exact superpose b3e95 b3e906965
          | exact resolve b3e906965 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95 b3e906965
        have b3e907017 : (σ y) = (M.op (σ y) x) ∨ x = (σ y) := by
          first
          | (have i₁ := b3e907005
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e907005
          | exact resolve b3e907005 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e907005
        have b3e907087 : (σ x) ≠ (M.op x x) ∨ (σ x) = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) x) := by
          first
          | (have i₁ := b3e29813 (σ x) x
             have i₂ := b3e906308
             grind)
          | exact superpose b3e906308 b3e29813
          | (have j0 := b3e29813 (σ x) x
             grind)
          | exact resolve b3e29813 b3e906308
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e906308
        have b3e907096 : (σ x) ≠ (M.op x x) ∨ (σ x) = (M.op (σ x) x) := by grind
        clear b3e907087
        have b3e907110 : x ≠ (σ x) ∨ (σ x) = (M.op (σ x) x) := by
          first
          | (have i₁ := b3e907096
             have i₂ := b3e62
             grind)
          | exact superpose b3e62 b3e907096
          | exact resolve b3e907096 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e907096
        have b3e907148 : (σ x) = (M.op (σ x) x) := by
          first
          | (have r₁ := b3e907110
             have r₂ := b3e906816
             grind)
          | exact resolve b3e907110 b3e906816
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e906816 b3e907110
        have b3e907238 : (σ y) ≠ (M.op x x) ∨ (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b3e29813 (σ y) x
             have i₂ := b3e906335
             grind)
          | exact superpose b3e906335 b3e29813
          | (have j0 := b3e29813 (σ y) x
             grind)
          | exact resolve b3e29813 b3e906335
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29813 b3e906335
        have b3e907247 : (σ y) ≠ (M.op x x) ∨ (σ y) = (M.op (σ y) x) := by grind
        clear b3e907238
        have b3e907263 : x ≠ (σ y) ∨ (σ y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b3e907247
             have i₂ := b3e62
             grind)
          | exact superpose b3e62 b3e907247
          | exact resolve b3e907247 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62 b3e907247
        have b3e907307 : (σ y) = (M.op (σ y) x) := by
          first
          | (have r₁ := b3e907263
             have r₂ := b3e907017
             grind)
          | exact resolve b3e907263 b3e907017
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e907017 b3e907263
        have b3e907716 : ∀ X0 : G, x ≠ (σ y) ∨ x = (k x (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e137 (σ y) x X0
             have i₂ := b3e907307
             grind)
          | exact superpose b3e907307 b3e137
          | (have j0 := b3e137 (σ y) x X0
             grind)
          | exact resolve b3e137 b3e907307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e137
        have b3e913297 : (k y (σ y)) = (σ (τ x)) ∨ y = (k y (σ y)) := by
          first
          | (have i₁ := b3e28 y y
             have i₂ := b3e906197
             grind)
          | exact superpose b3e906197 b3e28
          | exact resolve b3e28 b3e906197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e906197
        have b3e913695 : y = (k y (σ y)) ∨ x = (k y (σ y)) := by
          first
          | (have i₁ := b3e913297
             have i₂ := b3e14 x
             grind)
          | exact superpose b3e14 b3e913297
          | exact resolve b3e913297 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e913297
        have b3e913841 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (M.op (σ y) X0) ∨ y = (M.op y (σ y)) ∨ x = (k y (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e14662 y (σ y) X0
             have i₂ := b3e913695
             grind)
          | exact superpose b3e913695 b3e14662
          | (have j0 := b3e14662 y (σ y) X0
             grind)
          | (have r₁ := b3e14662 y (σ y) x
             have r₂ := b3e913695
             grind)
          | exact resolve b3e14662 b3e913695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14662 b3e913695
        have b3e913844 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ y = (M.op y (σ y)) ∨ x = (k y (σ y)) := by
          intro X0
          first
          | (have j0 := b3e913841 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e913841
        have b3e913856 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) ∨ y = (M.op y (σ y)) ∨ x = (k y (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e913844 X0
             have i₂ := b3e67 X0
             grind)
          | exact superpose b3e67 b3e913844
          | exact resolve b3e913844 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e913844
        have b3e913874 : ∀ X0 : G, y = (M.op x (σ x)) ∨ (M.op x X0) = (M.op (σ y) X0) ∨ x = (k y (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e913856 X0
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e913856
          | (have j0 := b3e913856 X0
             grind)
          | exact resolve b3e913856 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60 b3e913856
        have b3e913889 : ∀ X0 : G, x = y ∨ (M.op x X0) = (M.op (σ y) X0) ∨ x = (k y (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e913874 X0
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e913874
          | (have j0 := b3e913874 X0
             grind)
          | exact resolve b3e913874 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e913874
        have b3e913899 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) ∨ x = (k y (σ y)) := by
          intro X0
          first
          | (have j0 := b3e913889 X0
             grind)
          | (have r₁ := b3e913889 X0
             have r₂ := b3e322649
             grind)
          | exact resolve b3e913889 b3e322649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e913889
        have b3e914837 : (σ (τ x)) = (k y (σ x)) ∨ y = (k y (σ x)) := by
          first
          | (have i₁ := b3e28 y x
             have i₂ := b3e906208
             grind)
          | exact superpose b3e906208 b3e28
          | exact resolve b3e28 b3e906208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e906208
        have b3e915205 : y = (k y (σ x)) ∨ x = (k y (σ x)) := by
          first
          | (have i₁ := b3e914837
             have i₂ := b3e14 x
             grind)
          | exact superpose b3e14 b3e914837
          | exact resolve b3e914837 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e914837
        have b3e915330 : y = (M.op y (σ x)) ∨ (σ x) = (M.op y (σ x)) ∨ y = (M.op y (σ x)) ∨ x = (k y (σ x)) := by
          first
          | (have i₁ := b3e13261 y
             have i₂ := b3e915205
             grind)
          | exact superpose b3e915205 b3e13261
          | (have j0 := b3e13261 y
             grind)
          | exact resolve b3e13261 b3e915205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13261 b3e915205
        have b3e915356 : y = (M.op y (σ x)) ∨ (σ x) = (M.op y (σ x)) ∨ x = (k y (σ x)) := by grind
        clear b3e915330
        have b3e915371 : y = (M.op x (σ x)) ∨ (σ x) = (M.op y (σ x)) ∨ x = (k y (σ x)) := by
          first
          | (have i₁ := b3e915356
             have i₂ := b3e67 (σ x)
             grind)
          | exact superpose b3e67 b3e915356
          | exact resolve b3e915356 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e915356
        have b3e915382 : x = y ∨ (σ x) = (M.op y (σ x)) ∨ x = (k y (σ x)) := by
          first
          | (have i₁ := b3e915371
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e915371
          | exact resolve b3e915371 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e915371
        have b3e915393 : (σ x) = (M.op y (σ x)) ∨ x = (k y (σ x)) := by
          first
          | (have r₁ := b3e915382
             have r₂ := b3e322649
             grind)
          | exact resolve b3e915382 b3e322649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e322649 b3e915382
        have b3e915398 : (σ x) = (M.op x (σ x)) ∨ x = (k y (σ x)) := by
          first
          | (have i₁ := b3e915393
             have i₂ := b3e67 (σ x)
             grind)
          | exact superpose b3e67 b3e915393
          | exact resolve b3e915393 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67 b3e915393
        have b3e915401 : x = (k y (σ x)) ∨ x = (σ x) := by
          first
          | (have i₁ := b3e915398
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e915398
          | exact resolve b3e915398 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e915398
        have b3e915661 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = (σ x) := by
          intro X0
          first
          | (have i₁ := b3e1280 y (σ x) x
             have i₂ := b3e915401
             grind)
          | exact superpose b3e915401 b3e1280
          | exact resolve b3e1280 b3e915401
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1280 b3e915401
        have b3e915818 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = (σ x) := by
          intro X0
          first
          | (have j0 := b3e915661 X0
             grind)
          | (have r₁ := b3e915661 X0
             have r₂ := b3e322650
             grind)
          | exact resolve b3e915661 b3e322650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e915661
        have b3e920279 : (σ y) = (M.op (σ x) x) ∨ x = (σ x) := by
          first
          | (have i₁ := b3e907307
             have i₂ := b3e915818 x
             grind)
          | exact superpose b3e915818 b3e907307
          | exact resolve b3e907307 b3e915818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e915818
        have b3e920747 : (σ x) = (σ y) ∨ x = (σ x) := by
          first
          | (have i₁ := b3e920279
             have i₂ := b3e907148
             grind)
          | exact superpose b3e907148 b3e920279
          | exact resolve b3e920279 b3e907148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e907148 b3e920279
        have b3e920806 : x = (σ x) := by
          first
          | (have r₁ := b3e920747
             have r₂ := b3e322650
             grind)
          | exact resolve b3e920747 b3e322650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e920747
        have b3e942698 : (σ y) = (M.op x (σ x)) ∨ x = (k y (σ y)) := by
          first
          | (have i₁ := b3e320543
             have i₂ := b3e913899 (σ x)
             grind)
          | exact superpose b3e913899 b3e320543
          | exact resolve b3e320543 b3e913899
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e320543 b3e913899
        have b3e943519 : x = (k y (σ y)) ∨ x = (σ y) := by
          first
          | (have i₁ := b3e942698
             have i₂ := b3e906170
             grind)
          | exact superpose b3e906170 b3e942698
          | exact resolve b3e942698 b3e906170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e906170 b3e942698
        have b3e944182 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ x = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e1293 y (σ y) x
             have i₂ := b3e943519
             grind)
          | exact superpose b3e943519 b3e1293
          | exact resolve b3e1293 b3e943519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1293 b3e943519
        have b3e944327 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ y) X0)) ∨ x = (σ y) := by
          intro X0
          first
          | (have j0 := b3e944182 X0
             grind)
          | (have r₁ := b3e944182 X0
             have r₂ := b3e322650
             grind)
          | exact resolve b3e944182 b3e322650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e944182
        have b3e944586 : ∀ X0 : G, x = (k x (M.op (σ y) X0)) ∨ x = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e944327 X0
             have i₂ := b3e920806
             grind)
          | exact superpose b3e920806 b3e944327
          | exact resolve b3e944327 b3e920806
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e944327
        have b3e944768 : ∀ X0 : G, x = (k x (M.op (σ y) X0)) := by
          intro X0
          first
          | (have j0 := b3e944586 X0
             have j1 := b3e907716 X0
             grind)
          | (have r₁ := b3e944586 X0
             have r₂ := b3e907716 X0
             grind)
          | exact resolve b3e944586 b3e907716
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e907716 b3e944586
        have b3e945048 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op (σ y) x) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e17917 x X0 (σ y)
             have i₂ := b3e944768 X0
             grind)
          | exact superpose b3e944768 b3e17917
          | (have j0 := b3e17917 x X0 (σ y)
             grind)
          | exact resolve b3e17917 b3e944768
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17917 b3e944768
        have b3e945059 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op (σ y) x) := by
          intro X0
          first
          | (have j0 := b3e945048 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e945048
        have b3e945068 : ∀ X0 : G, x = (M.op x X0) ∨ x = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e945059 X0
             have i₂ := b3e907307
             grind)
          | exact superpose b3e907307 b3e945059
          | (have j0 := b3e945059 X0
             grind)
          | exact resolve b3e945059 b3e907307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e907307 b3e945059
        have b3e945417 : (σ x) ≠ (σ x) ∨ x = (σ y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e945068 y
             grind)
          | exact superpose b3e945068 b3e23
          | exact resolve b3e23 b3e945068
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e945068
        have b3e945970 : x = (σ y) := by grind
        clear b3e945417
        have b3e946297 : x ≠ (σ x) := by
          first
          | (have i₁ := b3e322650
             have i₂ := b3e945970
             grind)
          | exact superpose b3e945970 b3e322650
          | exact resolve b3e322650 b3e945970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e322650 b3e945970
        have b3e946763 : False := by grind
        exact b3e946763
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
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
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e28 X0 X1
               grind)
            | exact superpose b4e28 b4e14
            | exact resolve b4e14 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
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
          have b4e35 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op X1 X0)) := by
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
          have b4e36 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b4e13 (M.op X0 X2) X3 (M.op x X1) X5
               have i₂ := b4e13 X0 X1 X2 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
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
          have b4e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e16 (M.op X0 X2) (M.op X3 X1)
               have i₂ := b4e13 X0 X1 X2 X3
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X0 X2) (M.op X3 X1)
               grind)
            | (have r₁ := b4e16 (M.op X0 X1) (M.op X3 X1)
               have r₂ := b4e13 X0 X1 X1 X3
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e39 x X1 X2 X3 x
               have i₂ := b4e13 X2 X1 x x
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e42 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e36 X0 x X2 X3 x
               have i₂ := b4e13 X0 X3 x x
               grind)
            | exact superpose b4e13 b4e36
            | exact resolve b4e36 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e48 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 x X1 (M.op x X0) X3
               have i₂ := b4e34 X0 x
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e50 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b4e48 x X1 x
               have i₂ := b4e13 y X1 x x
               grind)
            | exact superpose b4e13 b4e48
            | exact resolve b4e48 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b4e106 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (M.op (M.op X2 X1) X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 (M.op X2 X1) X0
               have i₂ := b4e41 X1 X0 X2
               grind)
            | exact superpose b4e41 b4e17
            | (have j0 := b4e17 (M.op X2 X1) X0
               grind)
            | (have r₁ := b4e17 (M.op X2 X1) X2
               have r₂ := b4e41 X1 X2 X2
               grind)
            | exact resolve b4e17 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e112 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e106 X0 X1 X2
               have j1 := b4e16 (M.op X2 X1) X0
               grind)
            | (have r₁ := b4e106 X1 X1 X2
               have r₂ := b4e16 (M.op X2 X1) X1
               grind)
            | exact resolve b4e106 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e106
          have b4e124 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e17 X0 y
               have i₂ := b4e50 X0
               grind)
            | exact superpose b4e50 b4e17
            | (have j0 := b4e17 X0 y
               grind)
            | exact resolve b4e17 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b4e124 X0
               have j1 := b4e16 X0 y
               grind)
            | (have r₁ := b4e124 X0
               have r₂ := b4e16 X0 y
               grind)
            | exact resolve b4e124 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124
          have b4e136 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e42 (σ y) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e42
            | exact resolve b4e42 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e196 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e35 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e35
            | exact resolve b4e35 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e287 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e33
            | exact resolve b4e33 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e326 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e40 X0 X1 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e443 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e68 y x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e68
            | (have j0 := b4e68 y x
               grind)
            | exact resolve b4e68 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e475 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) (σ X1)
               have i₂ := b4e68 X0 X1
               grind)
            | exact superpose b4e68 b4e17
            | (have j0 := b4e17 (σ X0) (σ X1)
               have j1 := b4e68 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X0) (σ X1)
               have r₂ := b4e68 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X0) (σ X0)
               have r₂ := b4e68 X0 X0
               grind)
            | exact resolve b4e17 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e486 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e488 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e475 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e475
          have b4e489 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e488 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e488
          have b4e491 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e489 X0 X1
               have j1 := b4e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b4e489 X0 X1
               have r₂ := b4e16 (σ X0) (σ X1)
               grind)
            | exact resolve b4e489 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e489
          have b4e505 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e491 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e491
            | (have j0 := b4e491 X0 X1
               grind)
            | exact resolve b4e491 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e491
          have b4e1091 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b4e112 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e1242 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e505 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e505
            | exact resolve b4e505 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1255 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e505 y x
               grind)
            | exact superpose b4e505 b4e24
            | (have j1 := b4e505 y x
               grind)
            | exact resolve b4e24 b4e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1257 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b4e136 (σ X0)
               have i₂ := b4e505 y X0
               grind)
            | exact superpose b4e505 b4e136
            | (have j1 := b4e505 y X0
               grind)
            | exact resolve b4e136 b4e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e505
          have b4e1307 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e1242 X0 X1
               have i₂ := b4e28 X0 X1
               grind)
            | exact superpose b4e28 b4e1242
            | (have j0 := b4e1242 X0 X1
               grind)
            | exact resolve b4e1242 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1242
          have b4e1310 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e1307 X0 X1
               have i₂ := b4e28 X0 X1
               grind)
            | exact superpose b4e28 b4e1307
            | (have j0 := b4e1307 X0 X1
               grind)
            | exact resolve b4e1307 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e1307
          have b4e1350 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e326 (σ x) (σ y) x
               have i₂ := b4e443
               grind)
            | exact superpose b4e443 b4e326
            | exact resolve b4e326 b4e443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e326
          have b4e1436 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e486 (τ X0) (τ X1)
               have i₂ := b4e287 X1 X0
               grind)
            | exact superpose b4e287 b4e486
            | (have j0 := b4e486 (τ X0) (τ X1)
               grind)
            | exact resolve b4e486 b4e287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287
          have b4e1468 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1436 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e1436
            | (have j0 := b4e1436 X0 X1
               grind)
            | exact resolve b4e1436 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1436
          have b4e1475 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1468 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1468
            | (have j0 := b4e1468 X0 X1
               grind)
            | exact resolve b4e1468 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1468
          have b4e1478 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1475 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1475
            | (have j0 := b4e1475 X0 X1
               grind)
            | exact resolve b4e1475 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1475
          have b4e1480 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1478 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e1478
            | (have j0 := b4e1478 X0 X1
               grind)
            | exact resolve b4e1478 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1478
          have b4e1481 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e1480 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e1480
            | (have j0 := b4e1480 X0 X1
               grind)
            | exact resolve b4e1480 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1480
          have b4e1482 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e1481 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1481
            | (have j0 := b4e1481 X0 X1
               grind)
            | exact resolve b4e1481 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1481
          have b4e4682 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by grind
          clear b4e1255
          have b4e5187 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e1310 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1310
            | exact resolve b4e1310 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1310
          have b4e5634 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1257 y
               grind)
            | exact superpose b4e1257 b4e20
            | (have j1 := b4e1257 y
               grind)
            | exact resolve b4e20 b4e1257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1257
          have b4e12645 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e1350 (σ x)
               have i₂ := b4e443
               grind)
            | exact superpose b4e443 b4e1350
            | exact resolve b4e1350 b4e443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e443 b4e1350
          have b4e12674 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
          clear b4e12645
          have b4e12692 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b4e12674
               have r₂ := b4e4682
               grind)
            | exact resolve b4e12674 b4e4682
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4682 b4e12674
          have b4e12710 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b4e12692
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e12692
            | exact resolve b4e12692 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12692
          have b4e12749 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b4e486 y y
               have i₂ := b4e12710
               grind)
            | exact superpose b4e12710 b4e486
            | (have j0 := b4e486 y y
               grind)
            | (have r₁ := b4e486 y y
               have r₂ := b4e12710
               grind)
            | exact resolve b4e486 b4e12710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e486 b4e12710
          have b4e12808 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
          clear b4e12749
          have b4e12809 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
          clear b4e12808
          have b4e12864 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b4e12809
               have i₂ := b4e136 (σ y)
               grind)
            | exact superpose b4e136 b4e12809
            | exact resolve b4e12809 b4e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136 b4e12809
          have b4e17274 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e12864
               grind)
            | exact superpose b4e12864 b4e20
            | exact resolve b4e20 b4e12864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12864
          have b4e24424 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (k y y) := by
            first
            | (have i₁ := b4e5634
               have i₂ := b4e5187 y y
               grind)
            | exact superpose b4e5187 b4e5634
            | (have j1 := b4e5187 y y
               grind)
            | exact resolve b4e5634 b4e5187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5187 b4e5634
          have b4e24433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (k y y) := by
            first
            | (have i₁ := b4e24424
               have i₂ := b4e50 y
               grind)
            | exact superpose b4e50 b4e24424
            | exact resolve b4e24424 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24424
          have b4e24434 : (σ y) = (σ (M.op y y)) ∨ y = (k y y) := by grind
          clear b4e24433
          have b4e24437 : (σ (M.op x y)) = (σ y) ∨ y = (k y y) := by
            first
            | (have i₁ := b4e24434
               have i₂ := b4e50 y
               grind)
            | exact superpose b4e50 b4e24434
            | exact resolve b4e24434 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24434
          have b4e24691 : (M.op x y) = (τ (σ y)) ∨ y = (k y y) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e24437
               grind)
            | exact superpose b4e24437 b4e14
            | exact resolve b4e14 b4e24437
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24437
          have b4e24839 : y = (M.op x y) ∨ y = (k y y) := by
            first
            | (have i₁ := b4e24691
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e24691
            | exact resolve b4e24691 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24691
          have b4e24861 : y = (k y y) := by
            first
            | (have j1 := b4e130 y
               grind)
            | (have r₁ := b4e24839
               have r₂ := b4e130 y
               grind)
            | exact resolve b4e24839 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130 b4e24839
          have b4e25195 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e1482 y y
               have i₂ := b4e24861
               grind)
            | exact superpose b4e24861 b4e1482
            | (have j0 := b4e1482 y y
               grind)
            | (have r₁ := b4e1482 y y
               have r₂ := b4e24861
               grind)
            | exact resolve b4e1482 b4e24861
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1482 b4e24861
          have b4e25196 : y ≠ y ∨ y = (M.op y y) := by grind
          clear b4e25195
          have b4e25197 : y = (M.op y y) := by grind
          clear b4e25196
          have b4e25211 : y = (M.op x y) := by
            first
            | (have i₁ := b4e25197
               have i₂ := b4e50 y
               grind)
            | exact superpose b4e50 b4e25197
            | exact resolve b4e25197 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50 b4e25197
          have b4e25537 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b4e17274
               have i₂ := b4e25211
               grind)
            | exact superpose b4e25211 b4e17274
            | exact resolve b4e17274 b4e25211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17274
          have b4e25581 : y = (k y x) := by
            first
            | (have i₁ := b4e1091 x y
               have i₂ := b4e25211
               grind)
            | exact superpose b4e25211 b4e1091
            | exact resolve b4e1091 b4e25211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1091 b4e25211
          have b4e25600 : (σ x) = (σ (k y x)) := by grind
          clear b4e25537
          have b4e25606 : (σ x) = (σ y) := by
            first
            | (have i₁ := b4e25600
               have i₂ := b4e25581
               grind)
            | exact superpose b4e25581 b4e25600
            | exact resolve b4e25600 b4e25581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25581 b4e25600
          have b4e28421 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e25606
               grind)
            | exact superpose b4e25606 b4e23
            | exact resolve b4e23 b4e25606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25606
          have b4e28562 : False := by grind
          exact b4e28562
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e49 : x ≠ x ∨ x = (M.op x y) ∨ x = (k x y) := by
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
          have b5e52 : x = (M.op x y) ∨ x = (k x y) := by grind
          clear b5e49
          have b5e55 : x = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e21
               grind)
            | exact resolve b5e52 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e277 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e59 x y
               grind)
            | exact superpose b5e59 b5e24
            | (have j1 := b5e59 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e59 x y
               grind)
            | exact resolve b5e24 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e294 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e277
          have b5e298 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e294
               have r₂ := b5e23
               grind)
            | exact resolve b5e294 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e294
          have b5e308 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e298
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e298
            | exact resolve b5e298 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e298
          have b5e310 : False := by grind
          exact b5e310
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b6e63 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
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
        have b6e65 : x = (M.op x y) ∨ x = (M.op y x) := by grind
        clear b6e63
        have b6e68 : x = (M.op y x) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e20
             grind)
          | exact resolve b6e65 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e71 : False := by grind
        exact b6e71
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e46 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e49 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e46
          have b7e52 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e49
               have r₂ := b7e23
               grind)
            | exact resolve b7e49 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
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
          have b7e66 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
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
          have b7e67 : x = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b7e66
          have b7e69 : x = (M.op y x) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e21
               grind)
            | exact resolve b7e67 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e71 : False := by grind
          exact b7e71
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e169 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e65 x y
               grind)
            | exact superpose b8e65 b8e24
            | (have j1 := b8e65 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e65 x y
               grind)
            | exact resolve b8e24 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e184 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e169
          have b8e188 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e184
               have r₂ := b8e23
               grind)
            | exact resolve b8e184 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e198 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e188
               grind)
            | exact superpose b8e188 b8e20
            | exact resolve b8e20 b8e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188
          have b8e266 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e198
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e198
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e198 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e198
          have b8e267 : x = (M.op y x) ∨ x = (M.op x y) := by grind
          clear b8e266
          have b8e268 : x = (M.op x y) := by
            first
            | (have r₁ := b8e267
               have r₂ := b8e22
               grind)
            | exact resolve b8e267 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e267
          have b8e269 : False := by grind
          exact b8e269

/-- `Equation4438`: `x ◇ (y ◇ x) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxy_pyx_Equation4438 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4438 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4438.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b1e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) (σ x)
             grind)
          | (have r₁ := b1e15 (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : (σ y) = (k (σ y) (σ x)) := by grind
        clear b1e25
        have b1e27 : x = (k x y) := by grind
        clear b1e24
        have b1e28 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e26
          | exact resolve b1e26 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
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
        have b1e33 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y x)
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e13
          | exact resolve b1e13 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e34 : y = (k y x) := by
          first
          | (have i₁ := b1e33
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e33
          | exact resolve b1e33 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) (M.op X2 X0)) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X2 X0) X0 X3
             have i₂ := b1e12 X0 X2 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e12 X0 (M.op X0 x) X3
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e12 X0 x X3
             have i₂ := b1e12 X0 x X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op y x) := by
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
        have b1e45 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 X1 x
             have i₂ := b1e12 X0 X2 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 X0) ∨ (M.op (M.op X2 X0) X0) = X0 ∨ (M.op (M.op X2 X0) X0) = (k (M.op X2 X0) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 (M.op X2 X0) X0
             have i₂ := b1e12 X0 X2 X1
             grind)
          | exact superpose b1e12 b1e16
          | (have j0 := b1e16 (M.op X2 X0) X0
             grind)
          | (have r₁ := b1e16 (M.op (M.op X0 X2) X0) X0
             have r₂ := b1e12 X0 (M.op X0 X2) X2
             grind)
          | exact resolve b1e16 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e51 : y ≠ y ∨ x = (M.op y x) ∨ (k y x) = (M.op y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e16
          | (have j0 := b1e16 y x
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e20
             grind)
          | exact resolve b1e16 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : x = (M.op y x) ∨ (k y x) = (M.op y x) := by grind
        clear b1e51
        have b1e53 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e50
        have b1e54 : x = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e34
             grind)
          | exact superpose b1e34 b1e52
          | exact resolve b1e52 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e52
        have b1e55 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e53
             have r₂ := b1e21
             grind)
          | exact resolve b1e53 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e56 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e55
          | exact resolve b1e55 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e57 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e56
          | exact resolve b1e56 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e56
        have b1e58 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e21
          | exact resolve b1e21 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ y) X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) (σ x) X0
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e12
          | exact resolve b1e12 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e61 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e61
          | exact resolve b1e61 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e78 : ∀ X1 : G, (M.op y x) = (M.op (M.op x X1) x) := by
          intro X1
          first
          | (have i₁ := b1e12 x x X1
             have i₂ := b1e44 x
             grind)
          | exact superpose b1e44 b1e12
          | exact resolve b1e12 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e110 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b1e162 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X0 X2) X3 X0
             have i₂ := b1e40 X0 X2 X1
             grind)
          | (have i₁ := b1e12 (M.op X0 X2) X3 X0
             have i₂ := b1e40 X0 X1 X2
             grind)
          | exact superpose b1e40 b1e12
          | exact resolve b1e12 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e164 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ X0 ∨ (M.op X0 X2) = (k (M.op X0 X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 (M.op X0 X2) X0
             have i₂ := b1e40 X0 X2 X1
             grind)
          | (have i₁ := b1e15 (M.op X0 X2) X0
             have i₂ := b1e40 X0 X1 X2
             grind)
          | exact superpose b1e40 b1e15
          | (have j0 := b1e15 (M.op X0 X1) X0
             grind)
          | exact resolve b1e15 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e198 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e45 (σ y) X0 (σ x)
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e45
          | exact resolve b1e45 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e199 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b1e45 y X0 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e45
          | exact resolve b1e45 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e200 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op X1 (M.op X0 x))) = (M.op (M.op X0 x) (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e45 (M.op X0 x) X1 x
             have i₂ := b1e44 X0
             grind)
          | exact superpose b1e44 b1e45
          | exact resolve b1e45 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e45
        have b1e225 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e198 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e198
          | exact resolve b1e198 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e198
        have b1e294 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X0 (M.op X2 X0)) ∨ (k X0 (M.op X0 (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X0 (M.op X0 (M.op X2 X0))
             have i₂ := b1e38 X0 X2 X1
             grind)
          | exact superpose b1e38 b1e15
          | (have j0 := b1e15 X0 (M.op X0 (M.op X2 X0))
             grind)
          | exact resolve b1e15 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e303 : ∀ X0 X2 : G, (k X0 (M.op X0 (M.op X2 X0))) = X0 := by
          intro X0 X2
          first
          | (have j0 := b1e294 X0 x X2
             grind)
          | (have r₁ := b1e294 X0 X2 x
             have r₂ := b1e12 X0 x X2
             grind)
          | exact resolve b1e294 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e294
        have b1e332 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e303 X0 x
             have i₂ := b1e12 X0 x X1
             grind)
          | exact superpose b1e12 b1e303
          | exact resolve b1e303 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e334 : y = (k y (M.op y y)) := by
          first
          | (have i₁ := b1e303 y x
             have i₂ := b1e199 x
             grind)
          | exact superpose b1e199 b1e303
          | exact resolve b1e303 b1e199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e199 b1e303
        have b1e617 : y = (k y (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e332 y x
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e332
          | exact resolve b1e332 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e632 : y = (k y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e617
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e617
          | exact resolve b1e617 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e617
        have b1e801 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op X0 x)) = (M.op (M.op X0 x) (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e37 x x X0 X1
             have i₂ := b1e78 x
             grind)
          | exact superpose b1e78 b1e37
          | exact resolve b1e37 b1e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e78
        have b1e1015 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e110 X1 X0
             have i₂ := b1e17 (σ X1) X0
             grind)
          | exact superpose b1e17 b1e110
          | (have j1 := b1e17 (σ X1) X0
             grind)
          | exact resolve b1e110 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e110
        have b1e1082 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (σ X0) (σ X1)
             have i₂ := b1e68 X0 X1
             grind)
          | exact superpose b1e68 b1e16
          | (have j0 := b1e16 (σ X0) (σ X1)
             have j1 := b1e68 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X0) (σ X1)
             have r₂ := b1e68 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X1) (σ X0)
             have r₂ := b1e68 X0 X1
             grind)
          | exact resolve b1e16 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1100 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e68 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1101 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e68 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e1102 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e1100 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1100
        have b1e1103 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e1082 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1082
        have b1e1104 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e1103 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1103
        have b1e1110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1104 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e1104
          | (have j0 := b1e1104 X0 X1
             grind)
          | exact resolve b1e1104 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1104
        have b1e4799 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e1102 y
             have i₂ := b1e632
             grind)
          | exact superpose b1e632 b1e1102
          | (have j0 := b1e1102 y
             grind)
          | exact resolve b1e1102 b1e632
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e632
        have b1e4801 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e1102 (τ X0)
             have i₂ := b1e30 X0 (τ X0)
             grind)
          | exact superpose b1e30 b1e1102
          | (have j0 := b1e1102 (τ X0)
             grind)
          | exact resolve b1e1102 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e1102
        have b1e4802 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
        clear b1e4799
        have b1e4805 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e4801 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e4801
          | (have j0 := b1e4801 X0
             grind)
          | exact resolve b1e4801 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4801
        have b1e4808 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e4805 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e4805
          | (have j0 := b1e4805 X0
             grind)
          | exact resolve b1e4805 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4805
        have b1e4895 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e225 (σ y)
             have i₂ := b1e4802
             grind)
          | exact superpose b1e4802 b1e225
          | exact resolve b1e225 b1e4802
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e6093 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e4802
             have i₂ := b1e4895
             grind)
          | exact superpose b1e4895 b1e4802
          | exact resolve b1e4802 b1e4895
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4802 b1e4895
        have b1e6143 : (σ x) = (σ y) ∨ y = (M.op y x) := by grind
        clear b1e6093
        have b1e6185 : y = (M.op y x) := by
          first
          | (have r₁ := b1e6143
             have r₂ := b1e58
             grind)
          | exact resolve b1e6143 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6143
        have b1e9473 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op y x)) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e200 X0 x
             have i₂ := b1e162 X0 X1 x x
             grind)
          | exact superpose b1e162 b1e200
          | exact resolve b1e200 b1e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e162 b1e200
        have b1e9667 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e9473 X0 X1
             have i₂ := b1e6185
             grind)
          | exact superpose b1e6185 b1e9473
          | exact resolve b1e9473 b1e6185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9473
        have b1e13240 : ∀ X0 X1 : G, (M.op X0 x) ≠ (M.op (M.op X0 x) y) ∨ (M.op (M.op X0 x) X1) = (k (M.op (M.op X0 x) X1) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e164 (M.op X0 x) X0 X1
             have i₂ := b1e9667 X0 x
             grind)
          | exact superpose b1e9667 b1e164
          | (have j0 := b1e164 (M.op X0 x) X1 X1
             grind)
          | exact resolve b1e164 b1e9667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e164
        have b1e13285 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op X0 x)) ≠ (M.op (M.op X0 x) y) ∨ (M.op X0 x) = (M.op (M.op (M.op X0 x) y) (M.op X0 x)) ∨ (M.op (M.op (M.op X0 x) y) (M.op X0 x)) = (k (M.op (M.op X0 x) y) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e48 (M.op X0 x) X1 (M.op (M.op X0 X1) X0)
             have i₂ := b1e9667 X0 X1
             grind)
          | exact superpose b1e9667 b1e48
          | exact resolve b1e48 b1e9667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48 b1e9667
        have b1e13361 : ∀ X0 : G, (M.op (M.op X0 x) (M.op y x)) ≠ (M.op (M.op X0 x) y) ∨ (M.op X0 x) = (M.op (M.op (M.op X0 x) y) (M.op X0 x)) ∨ (M.op (M.op (M.op X0 x) y) (M.op X0 x)) = (k (M.op (M.op X0 x) y) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e13285 X0 x
             have i₂ := b1e801 X0 x
             grind)
          | exact superpose b1e801 b1e13285
          | (have j0 := b1e13285 X0 x
             grind)
          | exact resolve b1e13285 b1e801
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13285
        have b1e13436 : ∀ X0 : G, (M.op (M.op X0 x) y) ≠ (M.op (M.op X0 x) y) ∨ (M.op X0 x) = (M.op (M.op (M.op X0 x) y) (M.op X0 x)) ∨ (M.op (M.op (M.op X0 x) y) (M.op X0 x)) = (k (M.op (M.op X0 x) y) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e13361 X0
             have i₂ := b1e6185
             grind)
          | exact superpose b1e6185 b1e13361
          | (have j0 := b1e13361 X0
             grind)
          | exact resolve b1e13361 b1e6185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13361
        have b1e13437 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) y) (M.op X0 x)) ∨ (M.op (M.op (M.op X0 x) y) (M.op X0 x)) = (k (M.op (M.op X0 x) y) (M.op X0 x)) := by
          intro X0
          first
          | (have j0 := b1e13436 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13436
        have b1e13487 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op y x)) ∨ (M.op (M.op (M.op X0 x) y) (M.op X0 x)) = (k (M.op (M.op X0 x) y) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e13437 X0
             have i₂ := b1e801 X0 y
             grind)
          | exact superpose b1e801 b1e13437
          | (have j0 := b1e13437 X0
             grind)
          | exact resolve b1e13437 b1e801
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13437
        have b1e13521 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) ∨ (M.op (M.op (M.op X0 x) y) (M.op X0 x)) = (k (M.op (M.op X0 x) y) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e13487 X0
             have i₂ := b1e6185
             grind)
          | exact superpose b1e6185 b1e13487
          | (have j0 := b1e13487 X0
             grind)
          | exact resolve b1e13487 b1e6185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13487
        have b1e13545 : ∀ X0 : G, (M.op (M.op X0 x) (M.op y x)) = (k (M.op (M.op X0 x) y) (M.op X0 x)) ∨ (M.op X0 x) = (M.op (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b1e13521 X0
             have i₂ := b1e801 X0 y
             grind)
          | exact superpose b1e801 b1e13521
          | (have j0 := b1e13521 X0
             grind)
          | exact resolve b1e13521 b1e801
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e801 b1e13521
        have b1e13559 : ∀ X0 : G, (M.op (M.op X0 x) y) = (k (M.op (M.op X0 x) y) (M.op X0 x)) ∨ (M.op X0 x) = (M.op (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b1e13545 X0
             have i₂ := b1e6185
             grind)
          | exact superpose b1e6185 b1e13545
          | (have j0 := b1e13545 X0
             grind)
          | exact resolve b1e13545 b1e6185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13545
        have b1e13568 : ∀ X0 : G, (M.op (M.op X0 x) y) = (k (M.op (M.op X0 x) y) (M.op X0 x)) := by
          intro X0
          first
          | (have j0 := b1e13559 X0
             have j1 := b1e13240 X0 y
             grind)
          | (have r₁ := b1e13559 X0
             have r₂ := b1e13240 X0 x
             grind)
          | exact resolve b1e13559 b1e13240
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13240 b1e13559
        have b1e34170 : (M.op y y) = (k (M.op y y) y) := by
          first
          | (have i₁ := b1e13568 y
             have i₂ := b1e6185
             grind)
          | exact superpose b1e6185 b1e13568
          | exact resolve b1e13568 b1e6185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6185 b1e13568
        have b1e60488 : (σ y) ≠ (σ y) ∨ (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
          first
          | (have i₁ := b1e1101 (M.op y y) y
             have i₂ := b1e334
             grind)
          | exact superpose b1e334 b1e1101
          | (have j0 := b1e1101 (M.op y y) y
             grind)
          | exact resolve b1e1101 b1e334
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1101
        have b1e60514 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) := by grind
        clear b1e60488
        have b1e769289 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e225 (σ (M.op y y))
             have i₂ := b1e60514
             grind)
          | exact superpose b1e60514 b1e225
          | exact resolve b1e225 b1e60514
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e225 b1e60514
        have b1e770441 : (σ x) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e64 (σ (M.op y y))
             have i₂ := b1e769289
             grind)
          | exact superpose b1e769289 b1e64
          | exact resolve b1e64 b1e769289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e769289
        have b1e771230 : (σ x) = (σ (k (M.op y y) y)) ∨ (σ x) = (σ (k y (M.op y y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e1110 (M.op y y) y
             have i₂ := b1e770441
             grind)
          | exact superpose b1e770441 b1e1110
          | exact resolve b1e1110 b1e770441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1110 b1e770441
        have b1e771706 : (σ x) = (σ (k (M.op y y) y)) ∨ (σ x) = (σ (k y (M.op y y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b1e771230
             have r₂ := b1e58
             grind)
          | exact resolve b1e771230 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e771230
        have b1e771855 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k y (M.op y y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e771706
             have i₂ := b1e34170
             grind)
          | exact superpose b1e34170 b1e771706
          | exact resolve b1e771706 b1e34170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34170 b1e771706
        have b1e771933 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e771855
             have i₂ := b1e334
             grind)
          | exact superpose b1e334 b1e771855
          | exact resolve b1e771855 b1e334
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e334 b1e771855
        have b1e771969 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
          first
          | (have r₁ := b1e771933
             have r₂ := b1e58
             grind)
          | exact resolve b1e771933 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e771933
        have b1e773125 : (τ (σ x)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e1015 (σ y) y
             have i₂ := b1e771969
             grind)
          | exact superpose b1e771969 b1e1015
          | exact resolve b1e1015 b1e771969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1015 b1e771969
        have b1e773552 : (τ (σ x)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
        clear b1e773125
        have b1e773976 : (τ (σ x)) = (k y (τ (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
          first
          | (have r₁ := b1e773552
             have r₂ := b1e58
             grind)
          | exact resolve b1e773552 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e773552
        have b1e774290 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e773976
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e773976
          | exact resolve b1e773976 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e773976
        have b1e774461 : (σ x) = (σ (M.op y y)) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e774290
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e774290
          | exact resolve b1e774290 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e774290
        have b1e775696 : (M.op y y) = (τ (σ x)) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e774461
             grind)
          | exact superpose b1e774461 b1e13
          | exact resolve b1e13 b1e774461
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e775767 : x = (k y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e775696
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e775696
          | exact resolve b1e775696 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e775696
        have b1e776190 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e775767
             grind)
          | exact superpose b1e775767 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e775767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e775767
        have b1e776221 : x = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b1e776190
        have b1e777109 : y = (k y (M.op x y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e332 y y
             have i₂ := b1e776221
             grind)
          | exact superpose b1e776221 b1e332
          | exact resolve b1e332 b1e776221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e332 b1e776221
        have b1e778053 : y = (k y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e777109
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e777109
          | exact resolve b1e777109 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e777109
        have b1e778396 : y = (M.op y y) := by
          first
          | (have j1 := b1e4808 y
             grind)
          | (have r₁ := b1e778053
             have r₂ := b1e4808 y
             grind)
          | exact resolve b1e778053 b1e4808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4808 b1e778053
        have b1e779461 : (σ x) = (σ y) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e774461
             have i₂ := b1e778396
             grind)
          | exact superpose b1e778396 b1e774461
          | exact resolve b1e774461 b1e778396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e774461
        have b1e779508 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e778396
             grind)
          | exact superpose b1e778396 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 y y
             have r₂ := b1e778396
             grind)
          | exact resolve b1e15 b1e778396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e778396
        have b1e780064 : y = (k y y) := by grind
        clear b1e779508
        have b1e780161 : x = (k y y) := by
          first
          | (have r₁ := b1e779461
             have r₂ := b1e58
             grind)
          | exact resolve b1e779461 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e779461
        have b1e780202 : x = y := by
          first
          | (have i₁ := b1e780161
             have i₂ := b1e780064
             grind)
          | exact superpose b1e780064 b1e780161
          | exact resolve b1e780161 b1e780064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e780064 b1e780161
        have b1e780715 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e780202
             grind)
          | exact superpose b1e780202 b1e58
          | exact resolve b1e58 b1e780202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e780202
        have b1e780925 : False := by grind
        exact b1e780925
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b2e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e815 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e65 y x
             grind)
          | exact superpose b2e65 b2e21
          | (have j1 := b2e65 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e65 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e65 x y
             grind)
          | exact resolve b2e21 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e844 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e815
        have b2e850 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e844
             have r₂ := b2e22
             grind)
          | exact resolve b2e844 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e844
        have b2e856 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e850
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e850
          | exact resolve b2e850 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e850
        have b2e857 : False := by grind
        exact b2e857
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e28 : (σ x) = (σ (k x y)) := by
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
        have b3e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e32 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e12 X0 (M.op X0 x) X3
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e12 X0 x X3
             have i₂ := b3e12 X0 x X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e12 y X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1 x
             have i₂ := b3e12 X0 X2 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : (k x y) = (τ (σ x)) := by
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
        have b3e45 : x = (k x y) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e44
          | exact resolve b3e44 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e51 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b3e52 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
        clear b3e51
        have b3e54 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e52
             have r₂ := b3e20
             grind)
          | exact resolve b3e52 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e56 : x = (M.op x y) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e54
          | exact resolve b3e54 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e59 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e20
          | exact resolve b3e20 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e17 (σ X1) (σ X0)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e73 : ∀ X1 : G, (M.op x y) = (M.op (M.op y X1) y) := by
          intro X1
          first
          | (have i₁ := b3e12 y x X1
             have i₂ := b3e38 x
             grind)
          | exact superpose b3e38 b3e12
          | exact resolve b3e12 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e80 : ∀ X1 : G, x = (M.op (M.op y X1) y) := by
          intro X1
          first
          | (have i₁ := b3e73 X1
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e73
          | exact resolve b3e73 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e91 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
        have b3e98 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e30 X1 X0
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e105 : ∀ X0 : G, x = (M.op y (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e12 y X0 x
             have i₂ := b3e80 x
             grind)
          | exact superpose b3e80 b3e12
          | exact resolve b3e12 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e153 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ X0 ∨ (M.op X0 X2) = (k (M.op X0 X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 (M.op X0 X2) X0
             have i₂ := b3e34 X0 X2 X1
             grind)
          | (have i₁ := b3e15 (M.op X0 X2) X0
             have i₂ := b3e34 X0 X1 X2
             grind)
          | exact superpose b3e34 b3e15
          | (have j0 := b3e15 (M.op X0 X1) X0
             grind)
          | exact resolve b3e15 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e203 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e39 (σ y) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e39
          | exact resolve b3e39 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e307 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X0 (M.op X2 X0)) ∨ (k X0 (M.op X0 (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X0 (M.op X0 (M.op X2 X0))
             have i₂ := b3e32 X0 X2 X1
             grind)
          | exact superpose b3e32 b3e15
          | (have j0 := b3e15 X0 (M.op X0 (M.op X2 X0))
             grind)
          | exact resolve b3e15 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e308 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X0 (M.op X2 X0)) ∨ (M.op (M.op X0 (M.op X2 X0)) X0) = X0 ∨ (M.op (M.op X0 (M.op X2 X0)) X0) = (k (M.op X0 (M.op X2 X0)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 (M.op X0 (M.op X2 X0)) X0
             have i₂ := b3e32 X0 X2 X1
             grind)
          | exact superpose b3e32 b3e16
          | (have j0 := b3e16 (M.op X0 (M.op X2 X0)) X0
             grind)
          | exact resolve b3e16 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e315 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X2 X0)) X0) = (k (M.op X0 (M.op X2 X0)) X0) ∨ (M.op (M.op X0 (M.op X2 X0)) X0) = X0 := by
          intro X0 X2
          first
          | (have j0 := b3e308 X0 x X2
             grind)
          | (have r₁ := b3e308 X0 X2 x
             have r₂ := b3e12 X0 x X2
             grind)
          | exact resolve b3e308 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308
        have b3e316 : ∀ X0 X2 : G, (k X0 (M.op X0 (M.op X2 X0))) = X0 := by
          intro X0 X2
          first
          | (have j0 := b3e307 X0 x X2
             grind)
          | (have r₁ := b3e307 X0 X2 x
             have r₂ := b3e12 X0 x X2
             grind)
          | exact resolve b3e307 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e307
        have b3e398 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b3e316 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e316
          | exact resolve b3e316 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e316
        have b3e643 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e91 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e91
          | exact resolve b3e91 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1069 : (k y (τ (M.op (σ y) (σ y)))) = (τ (σ y)) := by
          first
          | (have i₁ := b3e98 y (M.op (σ y) (σ y))
             have i₂ := b3e398
             grind)
          | exact superpose b3e398 b3e98
          | exact resolve b3e98 b3e398
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e398
        have b3e1073 : y = (k y (τ (M.op (σ y) (σ y)))) := by
          first
          | (have i₁ := b3e1069
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1069
          | exact resolve b3e1069 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1069
        have b3e1122 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 (σ X0) (σ X1)
             have i₂ := b3e65 X0 X1
             grind)
          | exact superpose b3e65 b3e16
          | (have j0 := b3e16 (σ X0) (σ X1)
             have j1 := b3e65 X0 X1
             grind)
          | (have r₁ := b3e16 (σ X0) (σ X1)
             have r₂ := b3e65 X0 X1
             grind)
          | (have r₁ := b3e16 (σ X1) (σ X0)
             have r₂ := b3e65 X0 X1
             grind)
          | exact resolve b3e16 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1141 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e65 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1142 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1143 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e1141 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1141
        have b3e1144 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e1122 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1122
        have b3e1145 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e1144 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1144
        have b3e1151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1145 X0 X1
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e1145
          | (have j0 := b3e1145 X0 X1
             grind)
          | exact resolve b3e1145 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1145
        have b3e1164 : y = (k y (τ (σ (k y y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e1073
             have i₂ := b3e65 y y
             grind)
          | exact superpose b3e65 b3e1073
          | (have j1 := b3e65 y y
             grind)
          | exact resolve b3e1073 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1073
        have b3e1170 : y = (k y (τ (σ (k y y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e1164
        have b3e1171 : y = (k y (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e1170
             have i₂ := b3e13 (k y y)
             grind)
          | exact superpose b3e13 b3e1170
          | exact resolve b3e1170 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1170
        have b3e4391 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e1143 (τ X0)
             have i₂ := b3e30 X0 (τ X0)
             grind)
          | exact superpose b3e30 b3e1143
          | (have j0 := b3e1143 (τ X0)
             grind)
          | exact resolve b3e1143 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1143
        have b3e4393 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e4391 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e4391
          | (have j0 := b3e4391 X0
             grind)
          | exact resolve b3e4391 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4391
        have b3e4396 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e4393 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e4393
          | (have j0 := b3e4393 X0
             grind)
          | exact resolve b3e4393 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4393
        have b3e23001 : y = (k y (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e1171
             have i₂ := b3e17 y y
             grind)
          | exact superpose b3e17 b3e1171
          | (have j1 := b3e17 (σ y) (σ y)
             grind)
          | exact resolve b3e1171 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1171
        have b3e23006 : y = (k y (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b3e23001
        have b3e74396 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1142 (τ X1) (τ X0)
             have i₂ := b3e643 X1 X0
             grind)
          | exact superpose b3e643 b3e1142
          | (have j0 := b3e1142 (τ X1) (τ X0)
             grind)
          | exact resolve b3e1142 b3e643
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e643 b3e1142
        have b3e74466 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e74396 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e74396
          | (have j0 := b3e74396 X0 X1
             grind)
          | exact resolve b3e74396 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74396
        have b3e74479 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e74466 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e74466
          | (have j0 := b3e74466 X0 X1
             grind)
          | exact resolve b3e74466 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74466
        have b3e74486 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e74479 X0 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e74479
          | (have j0 := b3e74479 X0 X1
             grind)
          | exact resolve b3e74479 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74479
        have b3e74489 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e74486 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e74486
          | (have j0 := b3e74486 X0 X1
             grind)
          | exact resolve b3e74486 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74486
        have b3e74491 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e74489 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e74489
          | (have j0 := b3e74489 X0 X1
             grind)
          | exact resolve b3e74489 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74489
        have b3e74493 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e74491 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e74491
          | (have j0 := b3e74491 X0 X1
             grind)
          | exact resolve b3e74491 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74491
        have b3e74813 : (M.op (M.op (σ y) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
          first
          | (have i₁ := b3e315 (σ y) x
             have i₂ := b3e203 x
             grind)
          | exact superpose b3e203 b3e315
          | exact resolve b3e315 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e315
        have b3e74835 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
          first
          | (have i₁ := b3e74813
             have i₂ := b3e33 (σ y)
             grind)
          | exact superpose b3e33 b3e74813
          | exact resolve b3e74813 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74813
        have b3e74939 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
          first
          | (have j1 := b3e153 (σ y) x (σ y)
             grind)
          | (have r₁ := b3e74835
             have r₂ := b3e153 (σ y) (σ y) x
             grind)
          | exact resolve b3e74835 b3e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153 b3e74835
        have b3e75094 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
          first
          | (have i₁ := b3e91 (M.op (σ y) (σ y)) y
             have i₂ := b3e74939
             grind)
          | exact superpose b3e74939 b3e91
          | exact resolve b3e91 b3e74939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91 b3e74939
        have b3e78063 : (τ (σ (k y y))) = (k (τ (σ (k y y))) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e75094
             have i₂ := b3e65 y y
             grind)
          | exact superpose b3e65 b3e75094
          | (have j1 := b3e65 y y
             grind)
          | exact resolve b3e75094 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e78073 : (τ (σ (k y y))) = (k (τ (σ (k y y))) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e78063
        have b3e78076 : (k y y) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e78073
             have i₂ := b3e13 (k y y)
             grind)
          | exact superpose b3e13 b3e78073
          | exact resolve b3e78073 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78073
        have b3e141709 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1151 X0 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1151
          | exact resolve b3e1151 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1151
        have b3e142365 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e141709 X0 X1
             have i₂ := b3e29 X0 X1
             grind)
          | exact superpose b3e29 b3e141709
          | (have j0 := b3e141709 X0 X1
             grind)
          | exact resolve b3e141709 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141709
        have b3e142404 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e142365 X0 X1
             have i₂ := b3e30 X0 X1
             grind)
          | exact superpose b3e30 b3e142365
          | (have j0 := b3e142365 X0 X1
             grind)
          | exact resolve b3e142365 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e142365
        have b3e460206 : y ≠ y ∨ (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e74493 y (M.op y y)
             have i₂ := b3e23006
             grind)
          | exact superpose b3e23006 b3e74493
          | (have j0 := b3e74493 y (M.op y y)
             grind)
          | (have r₁ := b3e74493 y (M.op y y)
             have r₂ := b3e23006
             grind)
          | exact resolve b3e74493 b3e23006
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23006 b3e74493
        have b3e460207 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b3e460206
        have b3e460211 : (M.op x y) = (M.op y y) ∨ y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e460207
             have i₂ := b3e38 y
             grind)
          | exact superpose b3e38 b3e460207
          | exact resolve b3e460207 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e460207
        have b3e460215 : x = (M.op y y) ∨ y = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e460211
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e460211
          | exact resolve b3e460211 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e460211
        have b3e460219 : x = y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e460215
             have i₂ := b3e80 y
             grind)
          | exact superpose b3e80 b3e460215
          | exact resolve b3e460215 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80 b3e460215
        have b3e460223 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b3e460219
             have r₂ := b3e59
             grind)
          | exact resolve b3e460219 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e460219
        have b3e460632 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e75094
             have i₂ := b3e460223
             grind)
          | exact superpose b3e460223 b3e75094
          | exact resolve b3e75094 b3e460223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e460223
        have b3e461057 : y = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e460632
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e460632
          | exact resolve b3e460632 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e460632
        have b3e461082 : x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have j1 := b3e4396 y
             grind)
          | (have r₁ := b3e461057
             have r₂ := b3e4396 y
             grind)
          | exact resolve b3e461057 b3e4396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e461057
        have b3e720579 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e142404 (σ X0) X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e142404
        have b3e720580 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e720579 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e720579
        have b3e720582 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e720580 X0
             have i₂ := b3e18 X0 X0
             grind)
          | exact superpose b3e18 b3e720580
          | (have j0 := b3e720580 X0
             grind)
          | exact resolve b3e720580 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e720580
        have b3e720592 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e720582 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e720582
          | exact resolve b3e720582 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e720679 : (σ (k y y)) = (M.op (σ y) (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e203 (σ y)
             have i₂ := b3e720582 y
             grind)
          | exact superpose b3e720582 b3e203
          | (have j1 := b3e720582 y
             grind)
          | exact resolve b3e203 b3e720582
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e203 b3e720582
        have b3e720861 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e720592 X0
             have i₂ := b3e30 X0 (τ X0)
             grind)
          | exact superpose b3e30 b3e720592
          | (have j0 := b3e720592 X0
             grind)
          | exact resolve b3e720592 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e720592
        have b3e720864 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e720861 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e720861
          | (have j0 := b3e720861 X0
             grind)
          | exact resolve b3e720861 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e720861
        have b3e720938 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b3e29 X0 (τ X0)
             have i₂ := b3e720864 (τ X0)
             grind)
          | exact superpose b3e720864 b3e29
          | (have j1 := b3e720864 (τ X0)
             grind)
          | exact resolve b3e29 b3e720864
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e720864
        have b3e721010 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b3e720938 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e720938
          | (have j0 := b3e720938 X0
             grind)
          | exact resolve b3e720938 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e720938
        have b3e722056 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e721010 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e721010
          | exact resolve b3e721010 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e721010
        have b3e722096 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e722056 X0
             have i₂ := b3e18 X0 X0
             grind)
          | exact superpose b3e18 b3e722056
          | (have j0 := b3e722056 X0
             grind)
          | exact resolve b3e722056 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e722056
        have b3e722761 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e98 (k X0 X0) X1
             have i₂ := b3e722096 X0
             grind)
          | exact superpose b3e722096 b3e98
          | (have j1 := b3e722096 X0
             grind)
          | exact resolve b3e98 b3e722096
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e722096
        have b3e722782 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e722761 X0 X1
             have i₂ := b3e98 (M.op X0 X0) X1
             grind)
          | exact superpose b3e98 b3e722761
          | (have j0 := b3e722761 X0 X1
             grind)
          | exact resolve b3e722761 b3e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98 b3e722761
        have b3e725386 : ∀ X0 X1 : G, (k (k X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e722782 X0 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e722782
          | (have j0 := b3e722782 X1 X1
             grind)
          | exact resolve b3e722782 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e722782
        have b3e726364 : (k y y) = (k (M.op y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e78076
             have i₂ := b3e725386 y y
             grind)
          | exact superpose b3e725386 b3e78076
          | (have j1 := b3e725386 x (σ y)
             grind)
          | exact resolve b3e78076 b3e725386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78076 b3e725386
        have b3e742270 : (M.op (σ y) (σ y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e33 (σ (k y y))
             have i₂ := b3e720679
             grind)
          | exact superpose b3e720679 b3e33
          | exact resolve b3e33 b3e720679
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e720679
        have b3e805042 : (k x y) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e726364
             have i₂ := b3e461082
             grind)
          | exact superpose b3e461082 b3e726364
          | exact resolve b3e726364 b3e461082
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e461082 b3e726364
        have b3e805043 : (k x y) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b3e805042
             have r₂ := b3e59
             grind)
          | exact resolve b3e805042 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e805042
        have b3e805044 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e805043
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e805043
          | exact resolve b3e805043 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e805043
        have b3e805408 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (k y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e75094
             have i₂ := b3e805044
             grind)
          | exact superpose b3e805044 b3e75094
          | exact resolve b3e75094 b3e805044
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e805044
        have b3e805566 : y = (k y y) ∨ x = (k y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e805408
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e805408
          | exact resolve b3e805408 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e805408
        have b3e805572 : x = (k y y) ∨ y = (M.op y y) := by
          first
          | (have j1 := b3e4396 y
             grind)
          | (have r₁ := b3e805566
             have r₂ := b3e4396 y
             grind)
          | exact resolve b3e805566 b3e4396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e805566
        have b3e805779 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e742270
             have i₂ := b3e805572
             grind)
          | exact superpose b3e805572 b3e742270
          | exact resolve b3e742270 b3e805572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e742270 b3e805572
        have b3e806081 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e805779
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e805779
          | exact resolve b3e805779 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e805779
        have b3e806082 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b3e806081
        have b3e809645 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e75094
             have i₂ := b3e806082
             grind)
          | exact superpose b3e806082 b3e75094
          | exact resolve b3e75094 b3e806082
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75094 b3e806082
        have b3e810064 : y = (k y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e809645
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e809645
          | exact resolve b3e809645 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e809645
        have b3e810075 : y = (M.op y y) := by
          first
          | (have j1 := b3e4396 y
             grind)
          | (have r₁ := b3e810064
             have r₂ := b3e4396 y
             grind)
          | exact resolve b3e810064 b3e4396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4396 b3e810064
        have b3e810491 : x = (M.op y y) := by
          first
          | (have i₁ := b3e105 y
             have i₂ := b3e810075
             grind)
          | exact superpose b3e810075 b3e105
          | exact resolve b3e105 b3e810075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105
        have b3e811579 : x = y := by
          first
          | (have i₁ := b3e810491
             have i₂ := b3e810075
             grind)
          | exact superpose b3e810075 b3e810491
          | exact resolve b3e810491 b3e810075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e810075 b3e810491
        have b3e811776 : False := by grind
        exact b3e811776
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x y) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e56 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          have b4e57 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
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
          have b4e59 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b4e57
          have b4e60 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b4e56
          have b4e61 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e59
               have r₂ := b4e21
               grind)
            | exact resolve b4e59 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e62 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e60
               have r₂ := b4e23
               grind)
            | exact resolve b4e60 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e63 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e62
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e62
            | exact resolve b4e62 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e64 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e63
               have i₂ := b4e61
               grind)
            | exact superpose b4e61 b4e63
            | exact resolve b4e63 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61 b4e63
          have b4e65 : False := by grind
          exact b4e65
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ x ∨ y = (k y x) := by
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
          have b5e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e763 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e58 x y
               grind)
            | exact superpose b5e58 b5e24
            | (have j1 := b5e58 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e58 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e58 y x
               grind)
            | exact resolve b5e24 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e791 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e763
          have b5e797 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e791
               have r₂ := b5e23
               grind)
            | exact resolve b5e791 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e791
          have b5e803 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e797
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e797
            | exact resolve b5e797 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e797
          have b5e804 : False := by grind
          exact b5e804
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
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
        have b6e58 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
        have b6e60 : x = (M.op y x) ∨ y = (M.op x y) := by grind
        clear b6e58
        have b6e63 : y = (M.op x y) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e21
             grind)
          | exact resolve b6e60 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e66 : False := by grind
        exact b6e66
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) := by
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
          have b7e69 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
          have b7e71 : y = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b7e69
          have b7e74 : x = (M.op y x) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e21
               grind)
            | exact resolve b7e71 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e77 : False := by grind
          exact b7e77
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e50 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e646 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e50 x y
               grind)
            | exact superpose b8e50 b8e24
            | (have j1 := b8e50 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e50 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e50 y x
               grind)
            | exact resolve b8e24 b8e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e677 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e646
          have b8e683 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e677
               have r₂ := b8e23
               grind)
            | exact resolve b8e677 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e677
          have b8e689 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e683
               grind)
            | exact superpose b8e683 b8e20
            | exact resolve b8e20 b8e683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e683
          have b8e890 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e689
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e689
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e689 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e689
          have b8e891 : y = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b8e890
          have b8e892 : x = (M.op y x) := by
            first
            | (have r₁ := b8e891
               have r₂ := b8e21
               grind)
            | exact resolve b8e891 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e891
          have b8e893 : False := by grind
          exact b8e893

/-- `Equation4509`: `x ◇ (y ◇ z) = (x ◇ x) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation4509 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4509 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4509.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
        intro X0 X1 X2 X3
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e34 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op x X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 x X0 X1 X2
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X3 : G, (M.op x X0) = (M.op x X3) := by
        intro X0 X3
        first
        | (have i₁ := b0e34 x x X3
           have i₂ := b0e34 x x X0
           grind)
        | (have i₁ := b0e34 X0 x x
           have i₂ := b0e34 X0 x (M.op X0 x)
           grind)
        | exact superpose b0e34 b0e34
        | exact resolve b0e34 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e56 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b0e57 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
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
      have b0e58 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e57 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e59 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e56 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e87 : ∀ X0 : G, x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e19
           have i₂ := b0e43 x X0
           grind)
        | (have i₁ := b0e19
           have i₂ := b0e43 X0 x
           grind)
        | exact superpose b0e43 b0e19
        | exact resolve b0e19 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e151 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e59 (σ X0)
           grind)
        | exact superpose b0e59 b0e17
        | exact resolve b0e17 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e153 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e151 X0
           have i₂ := b0e58 X0
           grind)
        | exact superpose b0e58 b0e151
        | exact resolve b0e151 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58 b0e151
      have b0e155 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e153 X0
           have i₂ := b0e87 X0
           grind)
        | exact superpose b0e87 b0e153
        | exact resolve b0e153 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e159 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e155 y
           grind)
        | exact superpose b0e155 b0e18
        | exact resolve b0e18 b0e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155
      have b0e167 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e159
           have i₂ := b0e87 y
           grind)
        | exact superpose b0e87 b0e159
        | exact resolve b0e159 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87 b0e159
      have b0e168 : False := by grind
      exact b0e168
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
          intro X0 X1 X2 X3
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e32 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op x X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 x X0 X1 X2
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X3 : G, (M.op x X0) = (M.op x X3) := by
          intro X0 X3
          first
          | (have i₁ := b1e32 x x X3
             have i₂ := b1e32 x x X0
             grind)
          | (have i₁ := b1e32 X0 x x
             have i₂ := b1e32 X0 x (M.op X0 x)
             grind)
          | exact superpose b1e32 b1e32
          | exact resolve b1e32 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e55 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e55 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e85 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e20
             have i₂ := b1e41 x X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e41 X0 x
             grind)
          | exact superpose b1e41 b1e20
          | exact resolve b1e20 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e118 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e17 X0 (σ x)
             grind)
          | exact superpose b1e17 b1e21
          | (have j1 := b1e17 X0 X0
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 (σ x) x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 X0 (σ x)
             grind)
          | exact resolve b1e21 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e121 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b1e118 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118
        have b1e214 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e24 X0 x
             have i₂ := b1e56 (τ X0)
             grind)
          | exact superpose b1e56 b1e24
          | exact resolve b1e24 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e56
        have b1e223 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e214 X0
             have i₂ := b1e85 (τ X0)
             grind)
          | exact superpose b1e85 b1e214
          | exact resolve b1e214 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85 b1e214
        have b1e810 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e223 (σ x)
             have i₂ := b1e121 (σ x)
             grind)
          | exact superpose b1e121 b1e223
          | (have j1 := b1e121 (σ x)
             grind)
          | exact resolve b1e223 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121 b1e223
        have b1e813 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e810
        have b1e817 : False := by grind
        exact b1e817
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
          intro X0 X1 X2 X3
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e29 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op x X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 x X0 X1 X2
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 X3 : G, (M.op x X0) = (M.op x X3) := by
          intro X0 X3
          first
          | (have i₁ := b2e29 x x X3
             have i₂ := b2e29 x x X0
             grind)
          | (have i₁ := b2e29 X0 x x
             have i₂ := b2e29 X0 x (M.op X0 x)
             grind)
          | exact superpose b2e29 b2e29
          | exact resolve b2e29 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e50 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
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
        have b2e52 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e50 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e77 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e20
             have i₂ := b2e38 x X0
             grind)
          | (have i₁ := b2e20
             have i₂ := b2e38 X0 x
             grind)
          | exact superpose b2e38 b2e20
          | exact resolve b2e20 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e111 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ x)
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 X0 (σ x)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e111 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e111
        have b2e180 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 x
             have i₂ := b2e52 (τ X0)
             grind)
          | exact superpose b2e52 b2e24
          | exact resolve b2e24 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e52
        have b2e189 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e180 X0
             have i₂ := b2e77 (τ X0)
             grind)
          | exact superpose b2e77 b2e180
          | exact resolve b2e180 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77 b2e180
        have b2e591 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e189 (σ x)
             have i₂ := b2e116 (σ x)
             grind)
          | exact superpose b2e116 b2e189
          | (have j1 := b2e116 (σ x)
             grind)
          | exact resolve b2e189 b2e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116 b2e189
        have b2e594 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e591
        have b2e598 : False := by grind
        exact b2e598
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ x) (σ x) X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X3 X4)) = (M.op (M.op X0 (M.op X1 X2)) X5) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b3e12 (M.op X0 X0) X3 X4 X5
             have i₂ := b3e12 X0 X1 X2 (M.op X0 X0)
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 y X0 X1 X2
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : ∀ X0 X3 : G, (M.op y X0) = (M.op y X3) := by
          intro X0 X3
          first
          | (have i₁ := b3e32 x x X3
             have i₂ := b3e32 x x X0
             grind)
          | (have i₁ := b3e32 X0 x x
             have i₂ := b3e32 X0 x (M.op X0 x)
             grind)
          | exact superpose b3e32 b3e32
          | exact resolve b3e32 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e85 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e21
             have i₂ := b3e41 y X0
             grind)
          | (have i₁ := b3e21
             have i₂ := b3e41 X0 y
             grind)
          | exact superpose b3e41 b3e21
          | exact resolve b3e21 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e114 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 X2 X0
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X0 X1
             have j1 := b3e17 X2 X2
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e119 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e114 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114
        have b3e137 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X0 X0) X2) := by
          intro X0 X2
          first
          | (have i₁ := b3e12 X0 y x X2
             have i₂ := b3e85 x
             grind)
          | exact superpose b3e85 b3e12
          | exact resolve b3e12 b3e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e163 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1 X2 x
             have i₂ := b3e137 X0 x
             grind)
          | exact superpose b3e137 b3e12
          | exact resolve b3e12 b3e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e171 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 y) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X0 X0) X1 X2 X3
             have i₂ := b3e137 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e137 b3e12
          | exact resolve b3e12 b3e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e172 : ∀ X0 X3 : G, (M.op X0 (σ x)) = (M.op (M.op X0 y) X3) := by
          intro X0 X3
          first
          | (have i₁ := b3e171 X0 x x X3
             have i₂ := b3e27 X0 (M.op x x)
             grind)
          | exact superpose b3e27 b3e171
          | exact resolve b3e171 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e235 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e27 (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e27
          | exact resolve b3e27 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e246 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e137 X0 x
             have i₂ := b3e27 X0 x
             grind)
          | exact superpose b3e27 b3e137
          | exact resolve b3e137 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e137
        have b3e928 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X3 X4)) ≠ (M.op (M.op X0 X0) (M.op X1 X2)) ∨ (M.op (M.op X0 (M.op X3 X4)) X5) = (k (M.op X0 (M.op X3 X4)) X5) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b3e15 (M.op X0 (M.op X3 X4)) X5
             have i₂ := b3e30 X0 X3 X4 X1 X2 (M.op X0 (M.op X3 X4))
             grind)
          | (have i₁ := b3e15 (M.op X4 X4) X1
             have i₂ := b3e30 X4 X1 X2 X4 X4 X5
             grind)
          | exact superpose b3e30 b3e15
          | (have j0 := b3e15 (M.op X0 (M.op X3 X4)) X5
             grind)
          | exact resolve b3e15 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e951 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X0 (M.op X3 X4)) X5) = (k (M.op X0 (M.op X3 X4)) X5) := by
          intro X0 X3 X4 X5
          first
          | (have j0 := b3e928 X0 x x X3 X4 X5
             grind)
          | (have r₁ := b3e928 X0 x x x x X5
             have r₂ := b3e12 X0 x x (M.op x x)
             grind)
          | exact resolve b3e928 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e928
        have b3e1037 : ∀ X0 X5 : G, (M.op (M.op X0 y) X5) = (k (M.op X0 y) X5) := by
          intro X0 X5
          first
          | (have i₁ := b3e951 X0 x x X5
             have i₂ := b3e163 X0 x x
             grind)
          | exact superpose b3e163 b3e951
          | exact resolve b3e951 b3e163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e163 b3e951
        have b3e1112 : ∀ X0 X5 : G, (M.op X0 (σ x)) = (k (M.op X0 y) X5) := by
          intro X0 X5
          first
          | (have i₁ := b3e1037 X0 X5
             have i₂ := b3e172 X0 X5
             grind)
          | exact superpose b3e172 b3e1037
          | exact resolve b3e1037 b3e172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e172 b3e1037
        have b3e1151 : ∀ X0 X5 : G, (M.op X0 y) = (k (M.op X0 y) X5) := by
          intro X0 X5
          first
          | (have i₁ := b3e1112 X0 X5
             have i₂ := b3e246 X0
             grind)
          | exact superpose b3e246 b3e1112
          | exact resolve b3e1112 b3e246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e246 b3e1112
        have b3e1198 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e1151 (σ x) x
             have i₂ := b3e235 y
             grind)
          | exact superpose b3e235 b3e1151
          | exact resolve b3e1151 b3e235
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e235 b3e1151
        have b3e1774 : ∀ X0 : G, (σ x) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e1198 (σ X0)
             grind)
          | exact superpose b3e1198 b3e18
          | exact resolve b3e18 b3e1198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1198
        have b3e1874 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e119 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119
        have b3e1875 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e1874 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1874
        have b3e1884 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e1875 X0
             have j1 := b3e15 X0 X0
             grind)
          | (have r₁ := b3e1875 X0
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e1875 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1875
        have b3e2163 : ∀ X0 : G, (k x X0) = (τ (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e13 (k x X0)
             have i₂ := b3e1774 X0
             grind)
          | exact superpose b3e1774 b3e13
          | exact resolve b3e13 b3e1774
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1774
        have b3e2164 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e2163 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e2163
          | exact resolve b3e2163 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2163
        have b3e2555 : x = (M.op x x) := by
          first
          | (have i₁ := b3e1884 x
             have i₂ := b3e2164 x
             grind)
          | exact superpose b3e2164 b3e1884
          | exact resolve b3e1884 b3e2164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1884 b3e2164
        have b3e2568 : False := by grind
        exact b3e2568
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X2 X3
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
          have b4e33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op y X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 y X0 X1 X2
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X0 X3 : G, (M.op y X0) = (M.op y X3) := by
            intro X0 X3
            first
            | (have i₁ := b4e38 x x X3
               have i₂ := b4e38 x x X0
               grind)
            | (have i₁ := b4e38 X0 x x
               have i₂ := b4e38 X0 x (M.op X0 x)
               grind)
            | exact superpose b4e38 b4e38
            | exact resolve b4e38 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e91 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e22
               have i₂ := b4e47 y X0
               grind)
            | (have i₁ := b4e22
               have i₂ := b4e47 X0 y
               grind)
            | exact superpose b4e47 b4e22
            | exact resolve b4e22 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e121 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X1
               have j1 := b4e18 X2 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e129 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e121 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121
          have b4e148 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X0 X0) X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e13 X0 y x X2
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e13
            | exact resolve b4e13 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e437 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e33 X0 x
               have i₂ := b4e148 X0 x
               grind)
            | exact superpose b4e148 b4e33
            | exact resolve b4e33 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148
          have b4e676 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e437 (σ x)
               grind)
            | exact superpose b4e437 b4e20
            | exact resolve b4e20 b4e437
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2280 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e129 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129
          have b4e2281 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e2280 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2280
          have b4e2291 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e2281 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e2281 X0
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e2281 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2281
          have b4e2399 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e2291 (σ X0)
               grind)
            | exact superpose b4e2291 b4e19
            | exact resolve b4e19 b4e2291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2402 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e25 X0 (τ X0)
               have i₂ := b4e2291 (τ X0)
               grind)
            | exact superpose b4e2291 b4e25
            | exact resolve b4e25 b4e2291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e2408 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e2402 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e2402
            | exact resolve b4e2402 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2402
          have b4e2409 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e2399 X0
               have i₂ := b4e2291 X0
               grind)
            | exact superpose b4e2291 b4e2399
            | exact resolve b4e2399 b4e2291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2399
          have b4e2413 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e2408 X0
               have i₂ := b4e2291 X0
               grind)
            | exact superpose b4e2291 b4e2408
            | exact resolve b4e2408 b4e2291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2291 b4e2408
          have b4e11505 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b4e2409 (M.op (τ X0) (τ X0))
               have i₂ := b4e2413 X0
               grind)
            | exact superpose b4e2413 b4e2409
            | exact resolve b4e2409 b4e2413
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2409 b4e2413
          have b4e11506 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e11505 X0
               have i₂ := b4e33 (τ X0) (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b4e33 b4e11505
            | exact resolve b4e11505 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11505
          have b4e11547 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e11506 X0
               have i₂ := b4e437 (τ X0)
               grind)
            | exact superpose b4e437 b4e11506
            | exact resolve b4e11506 b4e437
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11506
          have b4e11567 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e11547 X0
               have i₂ := b4e33 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e33 b4e11547
            | exact resolve b4e11547 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e11547
          have b4e11579 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e11567 X0
               have i₂ := b4e437 X0
               grind)
            | exact superpose b4e437 b4e11567
            | exact resolve b4e11567 b4e437
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e437 b4e11567
          have b4e11917 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e11579 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e11579
            | exact resolve b4e11579 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11579
          have b4e14368 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e676
               have i₂ := b4e11917 x
               grind)
            | exact superpose b4e11917 b4e676
            | (have r₁ := b4e676
               have r₂ := b4e11917 x
               grind)
            | exact resolve b4e676 b4e11917
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e676 b4e11917
          have b4e14388 : False := by grind
          exact b4e14388
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X2 X3
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e35 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op y X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 y X0 X1 X2
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X3 : G, (M.op y X0) = (M.op y X3) := by
            intro X0 X3
            first
            | (have i₁ := b5e35 x x X3
               have i₂ := b5e35 x x X0
               grind)
            | (have i₁ := b5e35 X0 x x
               have i₂ := b5e35 X0 x (M.op X0 x)
               grind)
            | exact superpose b5e35 b5e35
            | exact resolve b5e35 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e56 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) := by
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
          have b5e58 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b5e56 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e83 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e44 y X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e44 X0 y
               grind)
            | exact superpose b5e44 b5e22
            | exact resolve b5e22 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e118 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e122 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b5e118 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118
          have b5e150 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e26 X0 y
               have i₂ := b5e58 (τ X0)
               grind)
            | exact superpose b5e58 b5e26
            | exact resolve b5e26 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e58
          have b5e159 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e150 X0
               have i₂ := b5e83 (τ X0)
               grind)
            | exact superpose b5e83 b5e150
            | exact resolve b5e150 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e150
          have b5e416 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e159 (σ y)
               have i₂ := b5e122 (σ y)
               grind)
            | exact superpose b5e122 b5e159
            | (have j1 := b5e122 (σ y)
               grind)
            | exact resolve b5e159 b5e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e122 b5e159
          have b5e419 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e416
          have b5e423 : False := by grind
          exact b5e423
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x) X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b6e40 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e43 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e40 (σ X0)
             grind)
          | exact superpose b6e40 b6e18
          | exact resolve b6e18 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X2 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X1
             have j1 := b6e17 X2 X2
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e76 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e69 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e84 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e25 (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e25
          | exact resolve b6e25 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e396 : ∀ X0 : G, (σ x) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e84 (σ X0)
             have i₂ := b6e43 X0
             grind)
          | exact superpose b6e43 b6e84
          | exact resolve b6e84 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e84
        have b6e711 : ∀ X0 : G, (k x X0) = (τ (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e13 (k x X0)
             have i₂ := b6e396 X0
             grind)
          | exact superpose b6e396 b6e13
          | exact resolve b6e13 b6e396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e396
        have b6e712 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b6e711 X0
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e711
          | exact resolve b6e711 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e711
        have b6e1164 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e76 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e1165 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e1164 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1164
        have b6e1172 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e1165 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e1165 X0
             have r₂ := b6e15 X0 x
             grind)
          | exact resolve b6e1165 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1165
        have b6e1231 : x = (M.op x x) := by
          first
          | (have i₁ := b6e712 x
             have i₂ := b6e1172 x
             grind)
          | exact superpose b6e1172 b6e712
          | exact resolve b6e712 b6e1172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e712 b6e1172
        have b6e1235 : False := by grind
        exact b6e1235
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e31 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) (σ y) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e26 X1 X0
               grind)
            | exact superpose b7e26 b7e14
            | exact resolve b7e14 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e48 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
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
          have b7e50 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e48 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e58 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e31 (σ y) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e31
            | exact resolve b7e31 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e95 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e18 X2 X0
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X0 X1
               have j1 := b7e18 X2 X2
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e105 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e95 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e266 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e45 y X0
               have i₂ := b7e50 X0
               grind)
            | exact superpose b7e50 b7e45
            | exact resolve b7e45 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45 b7e50
          have b7e275 : ∀ X0 : G, (τ (σ y)) = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e266 X0
               have i₂ := b7e58 X0
               grind)
            | exact superpose b7e58 b7e266
            | exact resolve b7e266 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e266
          have b7e277 : ∀ X0 : G, y = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e275 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e275
            | exact resolve b7e275 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e275
          have b7e388 : ∀ X0 : G, y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e277 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e277
            | exact resolve b7e277 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e277
          have b7e1386 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e105 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e1387 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e1386 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1386
          have b7e1395 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e1387 X0
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e1387 X0
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e1387 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1387
          have b7e1458 : y = (M.op y y) := by
            first
            | (have i₁ := b7e388 y
               have i₂ := b7e1395 y
               grind)
            | exact superpose b7e1395 b7e388
            | exact resolve b7e388 b7e1395
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e388 b7e1395
          have b7e1461 : False := by grind
          exact b7e1461
        · have b8e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X2 X3
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e33 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X4) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e13 X0 x x X4
               have i₂ := b8e13 X0 x x X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e85 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ x)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e93 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e85 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e240 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 X0 X1 x
               have i₂ := b8e93 X0
               grind)
            | exact superpose b8e93 b8e33
            | (have j1 := b8e93 X0
               grind)
            | exact resolve b8e33 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e23349 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e240 (σ y) (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e240 (σ y) X0 (σ y)
               grind)
            | exact superpose b8e240 b8e24
            | (have j1 := b8e240 (σ y) x x
               grind)
            | exact resolve b8e24 b8e240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e23392 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e93 X0
               have i₂ := b8e240 X0 X0 X1
               grind)
            | (have i₁ := b8e93 X0
               have i₂ := b8e240 X0 X1 X0
               grind)
            | exact superpose b8e240 b8e93
            | (have j0 := b8e93 X0
               have j1 := b8e240 X0 X1 x
               grind)
            | exact resolve b8e93 b8e240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93 b8e240
          have b8e23612 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have j0 := b8e23392 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23392
          have b8e23632 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j1 := b8e23612 (σ y) x
               grind)
            | (have r₁ := b8e23349 x
               have r₂ := b8e23612 (σ y) x
               grind)
            | exact resolve b8e23349 b8e23612
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23349 b8e23612
          have b8e23637 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e23632
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e23632
            | exact resolve b8e23632 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23632
          have b8e27998 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e23637
               grind)
            | exact superpose b8e23637 b8e20
            | exact resolve b8e20 b8e23637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23637
          have b8e29543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e27998
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e27998
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e27998 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27998
          have b8e29556 : y = (M.op y y) ∨ x = (M.op x x) := by grind
          clear b8e29543
          have b8e29563 : x = (M.op x x) := by
            first
            | (have r₁ := b8e29556
               have r₂ := b8e22
               grind)
            | exact resolve b8e29556 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29556
          have b8e29564 : False := by grind
          exact b8e29564

/-- `Equation4520`: `x ◇ (y ◇ z) = (x ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_x_x_pxy_Equation4520 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4520 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4520.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
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
        clear b1e29
        have b1e36 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2 X3 X5
          first
          | (have i₁ := b1e12 X3 (M.op X0 x) X2 X5
             have i₂ := b1e12 X0 X1 X2 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (σ x) (σ y) X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b1e12 X0 x X2 X4
             have i₂ := b1e12 X0 x X2 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 x X0 X1 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 X1 X2 x
             have i₂ := b1e12 X0 X3 X2 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (k X0 (M.op X3 X2)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e15 X0 (M.op X3 X2)
             have i₂ := b1e12 X0 X3 X2 X1
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 X0 (M.op X3 X2)
             grind)
          | (have r₁ := b1e15 (M.op X0 (M.op X1 X2)) X2
             have r₂ := b1e12 X0 X1 X2 (M.op X1 X2)
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : x = (M.op x x) := by
          first
          | (have i₁ := b1e43 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e43
          | exact resolve b1e43 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X2) ∨ (M.op (M.op X0 X1) X2) = X0 ∨ (k X0 (M.op X3 X2)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e16 X0 (M.op X1 X2)
             have i₂ := b1e12 X0 X1 X2 X3
             grind)
          | exact superpose b1e12 b1e16
          | (have j0 := b1e16 X0 (M.op X3 X2)
             grind)
          | (have r₁ := b1e16 X0 (M.op (M.op X0 X3) X2)
             have r₂ := b1e12 X0 (M.op X0 X3) X2 X3
             grind)
          | exact resolve b1e16 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X2) ∨ (k X0 (M.op X3 X2)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b1e57 X0 X1 X2 X3
             have j1 := b1e46 X0 X1 X2 X3
             grind)
          | (have r₁ := b1e57 X0 X1 X2 X3
             have r₂ := b1e46 X0 X1 X2 X3
             grind)
          | exact resolve b1e57 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e57
        have b1e69 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e50
             grind)
          | exact resolve b1e15 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e70 : x = (k x x) := by grind
        clear b1e69
        have b1e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e110 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e37 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e37
          | exact resolve b1e37 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e113 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (σ y) x
             have i₂ := b1e37 X0 x
             grind)
          | exact superpose b1e37 b1e12
          | exact resolve b1e12 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e124 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e110
             grind)
          | exact superpose b1e110 b1e15
          | (have j0 := b1e15 (σ y) (σ y)
             grind)
          | (have r₁ := b1e15 (σ y) (σ y)
             have r₂ := b1e110
             grind)
          | exact resolve b1e15 b1e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e110
        have b1e125 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e124
        have b1e126 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e125
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e125
          | exact resolve b1e125 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e125
        have b1e150 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 (σ x) X0 X1 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e38
          | exact resolve b1e38 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e200 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e126
             grind)
          | exact superpose b1e126 b1e13
          | exact resolve b1e13 b1e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126
        have b1e202 : y = (k y y) := by
          first
          | (have i₁ := b1e200
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e200
          | exact resolve b1e200 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e200
        have b1e238 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e202
             grind)
          | exact superpose b1e202 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e202
        have b1e239 : y = (M.op y y) := by grind
        clear b1e238
        have b1e275 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e44 X0 X1 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e44
          | exact resolve b1e44 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e277 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e44 X0 X1 x x
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e44
          | exact resolve b1e44 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e351 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 y X0 X1 y
             have i₂ := b1e239
             grind)
          | exact superpose b1e239 b1e38
          | exact resolve b1e38 b1e239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e354 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e44 X0 X1 y y
             have i₂ := b1e239
             grind)
          | exact superpose b1e239 b1e44
          | exact resolve b1e44 b1e239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e356 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e354 X0 x
             have i₂ := b1e275 X0 x
             grind)
          | exact superpose b1e275 b1e354
          | exact resolve b1e354 b1e275
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e275 b1e354
        have b1e393 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op X0 (M.op X2 x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e36 X2 x y X0 X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e36
          | exact resolve b1e36 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e489 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e393 X0 X1 x
             have i₂ := b1e277 X0 x
             grind)
          | exact superpose b1e277 b1e393
          | exact resolve b1e393 b1e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e277 b1e393
        have b1e523 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e489 X0 X1
             have i₂ := b1e356 (M.op X0 X1)
             grind)
          | exact superpose b1e356 b1e489
          | exact resolve b1e489 b1e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e489
        have b1e561 : y = (M.op y x) := by
          first
          | (have i₁ := b1e239
             have i₂ := b1e356 y
             grind)
          | exact superpose b1e356 b1e239
          | exact resolve b1e239 b1e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e239 b1e356
        have b1e2595 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b1e65 X0 X1 X2 (M.op X0 X1)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e2675 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e2595 (σ x) (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e2595
          | exact resolve b1e2595 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2905 : ∀ X0 X1 : G, (M.op x (σ X1)) = (M.op x (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e43 (σ X0) (σ X1)
             have i₂ := b1e73 X0 X1
             grind)
          | exact superpose b1e73 b1e43
          | (have j1 := b1e73 X0 X1
             grind)
          | exact resolve b1e43 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2918 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2919 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e2958 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
        have b1e2962 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e34 X0 X1
             have i₂ := b1e17 X0 (σ X1)
             grind)
          | exact superpose b1e17 b1e34
          | (have j1 := b1e17 X0 (σ X1)
             grind)
          | exact resolve b1e34 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e18179 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e2918 x x
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e2918
          | (have j0 := b1e2918 x x
             grind)
          | exact resolve b1e2918 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e2918
        have b1e18195 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e18179
        have b1e18196 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e18195
        have b1e18236 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e150 (σ x) X0
             have i₂ := b1e18196
             grind)
          | exact superpose b1e18196 b1e150
          | exact resolve b1e150 b1e18196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e150
        have b1e18253 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e44 X0 X1 (σ x) (σ x)
             have i₂ := b1e18196
             grind)
          | exact superpose b1e18196 b1e44
          | exact resolve b1e44 b1e18196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e18318 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ (M.op (M.op X0 X1) X2)) = (M.op (σ X0) (σ (M.op (M.op X0 X1) X2))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X1) X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e2919 X0 (M.op (M.op X0 X1) X2)
             have i₂ := b1e2595 X0 X1 X2
             grind)
          | exact superpose b1e2595 b1e2919
          | (have j0 := b1e2919 X0 (M.op (M.op X0 X1) X2)
             grind)
          | exact resolve b1e2919 b1e2595
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2595
        have b1e18362 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e2919 (τ X0) (τ X1)
             have i₂ := b1e2958 X1 X0
             grind)
          | exact superpose b1e2958 b1e2919
          | (have j0 := b1e2919 (τ X0) (τ X1)
             grind)
          | exact resolve b1e2919 b1e2958
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2919
        have b1e18436 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (σ X0) (σ (M.op (M.op X0 X1) X2))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X1) X2))) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e18318 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18318
        have b1e18446 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e18362 X0 X1
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e18362
          | (have j0 := b1e18362 X0 X1
             grind)
          | exact resolve b1e18362 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18362
        have b1e18464 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e18446 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18446
          | (have j0 := b1e18446 X0 X1
             grind)
          | exact resolve b1e18446 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18446
        have b1e18473 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e18464 X0 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18464
          | (have j0 := b1e18464 X0 X1
             grind)
          | exact resolve b1e18464 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18464
        have b1e18475 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e18473 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18473
          | (have j0 := b1e18473 X0 X1
             grind)
          | exact resolve b1e18473 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18473
        have b1e18477 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e18475 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e18475
          | (have j0 := b1e18475 X0 X1
             grind)
          | exact resolve b1e18475 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18475
        have b1e18479 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e18477 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18477
          | (have j0 := b1e18477 X0 X1
             grind)
          | exact resolve b1e18477 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18477
        have b1e23051 : ∀ X0 X1 : G, (M.op x (σ (τ X1))) = (M.op x (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e2905 (τ X0) (τ X1)
             have i₂ := b1e2958 X1 X0
             grind)
          | exact superpose b1e2958 b1e2905
          | (have j0 := b1e2905 (τ X0) (τ X1)
             grind)
          | exact resolve b1e2905 b1e2958
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2905 b1e2958
        have b1e23204 : ∀ X0 X1 : G, (M.op x (σ (τ X1))) = (M.op x (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e23051 X0 X1
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e23051
          | (have j0 := b1e23051 X0 X1
             grind)
          | exact resolve b1e23051 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23051
        have b1e23227 : ∀ X0 X1 : G, (M.op x X1) = (M.op x (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e23204 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e23204
          | (have j0 := b1e23204 X0 X1
             grind)
          | exact resolve b1e23204 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23204
        have b1e23245 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op x X1) = (M.op x (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e23227 X0 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e23227
          | (have j0 := b1e23227 X0 X1
             grind)
          | exact resolve b1e23227 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23227
        have b1e23260 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op x X1) = (M.op x (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e23245 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e23245
          | (have j0 := b1e23245 X0 X1
             grind)
          | exact resolve b1e23245 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23245
        have b1e23264 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (M.op x X1) = (M.op x (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e23260 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e23260
          | (have j0 := b1e23260 X0 X1
             grind)
          | exact resolve b1e23260 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23260
        have b1e23265 : ∀ X0 X1 : G, (M.op x X1) = (M.op x (k X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e23264 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e23264
          | (have j0 := b1e23264 X0 X1
             grind)
          | exact resolve b1e23264 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23264
        have b1e141017 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op (M.op y X0) X1))) ∨ (σ y) = (M.op (σ y) (σ (M.op (M.op y X0) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e2675 (σ (M.op (M.op y X0) X1))
             have i₂ := b1e18436 y X0 X1
             grind)
          | exact superpose b1e18436 b1e2675
          | (have j1 := b1e18436 y X0 X1
             grind)
          | exact resolve b1e2675 b1e18436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2675 b1e18436
        have b1e141361 : ∀ X0 X1 : G, (σ x) = (σ (k x (M.op (M.op y X0) X1))) ∨ (σ y) = (M.op (σ y) (σ (M.op (M.op y X0) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e141017 X0 X1
             have i₂ := b1e18 x (M.op (M.op y X0) X1)
             grind)
          | exact superpose b1e18 b1e141017
          | (have j0 := b1e141017 X0 X1
             grind)
          | exact resolve b1e141017 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141017
        have b1e141490 : ∀ X0 X1 : G, (σ x) = (σ (k x (M.op y X1))) ∨ (σ y) = (M.op (σ y) (σ (M.op (M.op y X0) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e141361 X0 X1
             have i₂ := b1e351 X0 X1
             grind)
          | exact superpose b1e351 b1e141361
          | (have j0 := b1e141361 X0 X1
             grind)
          | exact resolve b1e141361 b1e351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141361
        have b1e141609 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ (M.op (M.op y X0) X1))) ∨ (σ x) = (σ (k x (M.op y X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e141490 X0 X1
             have i₂ := b1e18236 (σ (M.op (M.op y X0) X1))
             grind)
          | exact superpose b1e18236 b1e141490
          | (have j0 := b1e141490 X0 X1
             grind)
          | exact resolve b1e141490 b1e18236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18236 b1e141490
        have b1e141663 : ∀ X1 : G, (σ y) = (M.op (σ x) (σ (M.op y X1))) ∨ (σ x) = (σ (k x (M.op y X1))) := by
          intro X1
          first
          | (have i₁ := b1e141609 x X1
             have i₂ := b1e351 x X1
             grind)
          | exact superpose b1e351 b1e141609
          | (have j0 := b1e141609 x X1
             grind)
          | exact resolve b1e141609 b1e351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e351 b1e141609
        have b1e153013 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ x)) (M.op y X0)) ∨ (σ y) = (σ (M.op y X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e2962 (σ x) (M.op y x)
             have i₂ := b1e141663 x
             grind)
          | exact superpose b1e141663 b1e2962
          | (have j1 := b1e141663 X0
             grind)
          | exact resolve b1e2962 b1e141663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2962
        have b1e153019 : ∀ X0 : G, (σ y) ≠ (σ (M.op y X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ (M.op y X0))) ∨ (σ x) = (σ (k x (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) (σ (M.op y x))
             have i₂ := b1e141663 x
             grind)
          | exact superpose b1e141663 b1e16
          | (have j0 := b1e16 (σ x) (σ (M.op y X0))
             have j1 := b1e141663 X0
             grind)
          | exact resolve b1e16 b1e141663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141663
        have b1e153344 : ∀ X0 : G, (σ y) ≠ (σ (M.op y X0)) ∨ (σ x) = (k (σ x) (σ (M.op y X0))) ∨ (σ x) = (σ (k x (M.op y X0))) := by
          intro X0
          first
          | (have j0 := b1e153019 X0
             grind)
          | (have r₁ := b1e153019 X0
             have r₂ := b1e23
             grind)
          | exact resolve b1e153019 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153019
        have b1e153345 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ x)) (M.op y X0)) ∨ (σ y) = (σ (M.op y X0)) ∨ (σ x) = (σ (k x (M.op y X0))) := by
          intro X0
          first
          | (have j0 := b1e153013 X0
             grind)
          | (have r₁ := b1e153013 X0
             have r₂ := b1e23
             grind)
          | exact resolve b1e153013 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153013
        have b1e153403 : ∀ X0 : G, (σ x) = (σ (k x (M.op y X0))) ∨ (σ y) ≠ (σ (M.op y X0)) ∨ (σ x) = (σ (k x (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e153344 X0
             have i₂ := b1e18 x (M.op y X0)
             grind)
          | exact superpose b1e18 b1e153344
          | (have j0 := b1e153344 X0
             grind)
          | exact resolve b1e153344 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153344
        have b1e153404 : ∀ X0 : G, (σ y) ≠ (σ (M.op y X0)) ∨ (σ x) = (σ (k x (M.op y X0))) := by
          intro X0
          first
          | (have j0 := b1e153403 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153403
        have b1e153405 : ∀ X0 : G, (τ (σ y)) = (k x (M.op y X0)) ∨ (σ y) = (σ (M.op y X0)) ∨ (σ x) = (σ (k x (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e153345 X0
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e153345
          | (have j0 := b1e153345 X0
             grind)
          | exact resolve b1e153345 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153345
        have b1e153441 : ∀ X0 : G, (τ (σ y)) = (k x (M.op y X0)) ∨ (σ x) = (σ (k x (M.op y X0))) := by
          intro X0
          first
          | (have j0 := b1e153405 X0
             have j1 := b1e153404 X0
             grind)
          | (have r₁ := b1e153405 X0
             have r₂ := b1e153404 X0
             grind)
          | exact resolve b1e153405 b1e153404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153404 b1e153405
        have b1e153461 : ∀ X0 : G, (σ x) = (σ (k x (M.op y X0))) ∨ y = (k x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e153441 X0
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e153441
          | (have j0 := b1e153441 X0
             grind)
          | exact resolve b1e153441 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153441
        have b1e154658 : ∀ X0 : G, (τ (σ x)) = (k x (M.op y X0)) ∨ y = (k x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e13 (k x (M.op y X0))
             have i₂ := b1e153461 X0
             grind)
          | exact superpose b1e153461 b1e13
          | (have j1 := b1e153461 X0
             grind)
          | exact resolve b1e13 b1e153461
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153461
        have b1e154812 : ∀ X0 : G, y = (k x (M.op y X0)) ∨ x = (k x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e154658 X0
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e154658
          | (have j0 := b1e154658 X0
             grind)
          | exact resolve b1e154658 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e154658
        have b1e155646 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) ∨ (M.op y X0) = (M.op x (M.op y X0)) ∨ x = (M.op x (M.op y X0)) ∨ x = (k x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e23265 x (M.op y X0)
             have i₂ := b1e154812 X0
             grind)
          | exact superpose b1e154812 b1e23265
          | (have j0 := b1e23265 x (M.op y X0)
             have j1 := b1e154812 X0
             grind)
          | exact resolve b1e23265 b1e154812
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23265 b1e154812
        have b1e155655 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) ∨ (M.op y X0) = (M.op x (M.op y X0)) ∨ x = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have j0 := b1e155646 X0
             have j1 := b1e18479 x (M.op y X0)
             grind)
          | (have r₁ := b1e155646 X0
             have r₂ := b1e18479 x (M.op y X0)
             grind)
          | exact resolve b1e155646 b1e18479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18479 b1e155646
        have b1e155687 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (M.op y X0) = (M.op x (M.op y X0)) ∨ x = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e155655 X0
             have i₂ := b1e43 y X0
             grind)
          | exact superpose b1e43 b1e155655
          | (have j0 := b1e155655 X0
             grind)
          | exact resolve b1e155655 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e155655
        have b1e155710 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op y X0) = (M.op x (M.op y X0)) ∨ x = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e155687 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e155687
          | (have j0 := b1e155687 X0
             grind)
          | exact resolve b1e155687 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e155687
        have b1e155722 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (M.op x X0) ∨ x = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e155710 X0
             have i₂ := b1e43 y X0
             grind)
          | exact superpose b1e43 b1e155710
          | (have j0 := b1e155710 X0
             grind)
          | exact resolve b1e155710 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e155710
        have b1e155730 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x X0) = (M.op y X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e155722 X0
             have i₂ := b1e43 y X0
             grind)
          | exact superpose b1e43 b1e155722
          | (have j0 := b1e155722 X0
             grind)
          | exact resolve b1e155722 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e155722
        have b1e155731 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b1e155730 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e155730
        have b1e156995 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op y x) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e523 y X0
             have i₂ := b1e155731 X0
             grind)
          | exact superpose b1e155731 b1e523
          | (have j1 := b1e155731 X0
             grind)
          | exact resolve b1e523 b1e155731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e155731
        have b1e157576 : ∀ X0 : G, y = (M.op (M.op x X0) x) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e156995 X0
             have i₂ := b1e561
             grind)
          | exact superpose b1e561 b1e156995
          | (have j0 := b1e156995 X0
             grind)
          | exact resolve b1e156995 b1e561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e561 b1e156995
        have b1e157767 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e157576 X0
             have i₂ := b1e523 x X0
             grind)
          | exact superpose b1e523 b1e157576
          | (have j0 := b1e157576 X0
             grind)
          | exact resolve b1e157576 b1e523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e523 b1e157576
        have b1e157848 : ∀ X0 : G, x = (M.op x X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e157767 X0
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e157767
          | (have j0 := b1e157767 X0
             grind)
          | exact resolve b1e157767 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50 b1e157767
        have b1e159563 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e18253 X0 x
             have i₂ := b1e157848 (σ x)
             grind)
          | exact superpose b1e157848 b1e18253
          | exact resolve b1e18253 b1e157848
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18253
        have b1e159580 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e113 X0 x
             have i₂ := b1e157848 (σ y)
             grind)
          | exact superpose b1e157848 b1e113
          | exact resolve b1e113 b1e157848
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e113 b1e157848
        have b1e226108 : (σ x) = (M.op (σ x) x) ∨ x = y := by
          first
          | (have i₁ := b1e18196
             have i₂ := b1e159563 (σ x)
             grind)
          | exact superpose b1e159563 b1e18196
          | exact resolve b1e18196 b1e159563
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18196 b1e159563
        have b1e229007 : (σ y) = (M.op (σ x) x) ∨ x = y := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e159580 (σ x)
             grind)
          | exact superpose b1e159580 b1e22
          | exact resolve b1e22 b1e159580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e159580
        have b1e230298 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b1e226108
             have i₂ := b1e229007
             grind)
          | exact superpose b1e229007 b1e226108
          | exact resolve b1e226108 b1e229007
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e226108 b1e229007
        have b1e230626 : (σ x) = (σ y) ∨ x = y := by grind
        clear b1e230298
        have b1e230730 : x = y := by
          first
          | (have r₁ := b1e230626
             have r₂ := b1e23
             grind)
          | exact resolve b1e230626 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e230626
        have b1e230942 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e230730
             grind)
          | exact superpose b1e230730 b1e23
          | exact resolve b1e23 b1e230730
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e230730
        have b1e231106 : False := by grind
        exact b1e231106
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x ≠ x ∨ x = (k x y) := by
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
        have b2e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e1732 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e203638 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1732 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1732
          | (have j0 := b2e1732 x y
             grind)
          | exact resolve b2e1732 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1732
        have b2e203650 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e203638
        have b2e203741 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e203650
             have r₂ := b2e22
             grind)
          | exact resolve b2e203650 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e203650
        have b2e203770 : False := by grind
        exact b2e203770
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
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
        have b3e24 : (σ (M.op x y)) ≠ (σ x) := by
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
        have b3e27 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e39 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2 X3 X5
          first
          | (have i₁ := b3e12 X3 (M.op X0 x) X2 X5
             have i₂ := b3e12 X0 X1 X2 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op X0 (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y) X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 x X0 X1 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 X1 X2 x
             have i₂ := b3e12 X0 X3 X2 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (k X0 (M.op X3 X2)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e15 X0 (M.op X3 X2)
             have i₂ := b3e12 X0 X3 X2 X1
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 X0 (M.op X3 X2)
             grind)
          | (have r₁ := b3e15 (M.op X0 (M.op X1 X2)) X2
             have r₂ := b3e12 X0 X1 X2 (M.op X1 X2)
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X3) ∨ (M.op X0 X3) = (k (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e15 (M.op X0 X3) X2
             have i₂ := b3e12 X0 X1 X2 X3
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 (M.op X0 X3) X2
             grind)
          | (have r₁ := b3e15 (M.op X0 (M.op X1 X2)) X2
             have r₂ := b3e12 X0 X1 X2 (M.op X1 X2)
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X2) ∨ (M.op (M.op X0 X1) X2) = X0 ∨ (k X0 (M.op X3 X2)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e16 X0 (M.op X1 X2)
             have i₂ := b3e12 X0 X1 X2 X3
             grind)
          | exact superpose b3e12 b3e16
          | (have j0 := b3e16 X0 (M.op X3 X2)
             grind)
          | (have r₁ := b3e16 X0 (M.op (M.op X0 X3) X2)
             have r₂ := b3e12 X0 (M.op X0 X3) X2 X3
             grind)
          | exact resolve b3e16 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X2) ∨ (k X0 (M.op X3 X2)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b3e51 X0 X1 X2 X3
             have j1 := b3e49 X0 X1 X2 X3
             grind)
          | (have r₁ := b3e51 X0 X1 X2 X3
             have r₂ := b3e49 X0 X1 X2 X3
             grind)
          | exact resolve b3e51 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e60 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b3e46 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e46
          | exact resolve b3e46 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e63 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op x X2) X0) := by
          intro X0 X2
          first
          | (have i₁ := b3e12 x x X0 X2
             have i₂ := b3e46 x X0
             grind)
          | exact superpose b3e46 b3e12
          | exact resolve b3e12 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70 : y = (M.op y y) := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e60
          | exact resolve b3e60 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b3e82 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b3e15 y y
             have i₂ := b3e70
             grind)
          | exact superpose b3e70 b3e15
          | (have j0 := b3e15 y y
             grind)
          | (have r₁ := b3e15 y y
             have r₂ := b3e70
             grind)
          | exact resolve b3e15 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e83 : y = (k y y) := by grind
        clear b3e82
        have b3e85 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e30 X0 X1
             have i₂ := b3e17 (τ X0) X1
             grind)
          | exact superpose b3e17 b3e30
          | (have j1 := b3e17 (τ X0) X1
             grind)
          | exact resolve b3e30 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e88 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e30 X0 X1
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e31 X1 X0
             grind)
          | exact superpose b3e31 b3e13
          | exact resolve b3e13 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e111 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e40 (M.op X0 X1) (σ y)
             have i₂ := b3e40 X0 X1
             grind)
          | exact superpose b3e40 b3e40
          | exact resolve b3e40 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e112 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e40 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e40
          | exact resolve b3e40 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e118 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (σ y) x
             have i₂ := b3e40 X0 x
             grind)
          | exact superpose b3e40 b3e12
          | exact resolve b3e12 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e130 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e112
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e112
          | exact resolve b3e112 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e112
        have b3e131 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e111 X0 X1
             have i₂ := b3e40 X0 (σ x)
             grind)
          | exact superpose b3e40 b3e111
          | exact resolve b3e111 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111
        have b3e139 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e130
             grind)
          | exact superpose b3e130 b3e15
          | (have j0 := b3e15 (σ x) (σ x)
             grind)
          | (have r₁ := b3e15 (σ x) (σ x)
             have r₂ := b3e130
             grind)
          | exact resolve b3e15 b3e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e140 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b3e139
        have b3e141 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e140
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e140
          | exact resolve b3e140 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e140
        have b3e214 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e141
             grind)
          | exact superpose b3e141 b3e13
          | exact resolve b3e13 b3e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141
        have b3e216 : x = (k x x) := by
          first
          | (have i₁ := b3e214
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e214
          | exact resolve b3e214 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e214
        have b3e246 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e216
             grind)
          | exact superpose b3e216 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e216
        have b3e247 : x = (M.op x x) := by grind
        clear b3e246
        have b3e282 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e47 X1 X2 (M.op X3 X0) x
             have i₂ := b3e46 X3 X0
             grind)
          | exact superpose b3e46 b3e47
          | exact resolve b3e47 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e283 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e47 X0 X1 y y
             have i₂ := b3e70
             grind)
          | exact superpose b3e70 b3e47
          | exact resolve b3e47 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e355 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e46 x x
             have i₂ := b3e247
             grind)
          | exact superpose b3e247 b3e46
          | exact resolve b3e46 b3e247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e359 : x = (M.op y x) := by
          first
          | (have i₁ := b3e355
             have i₂ := b3e247
             grind)
          | exact superpose b3e247 b3e355
          | exact resolve b3e355 b3e247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e355
        have b3e392 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X3 X0)) = (M.op X1 (M.op X4 (M.op y X0))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e39 X4 x (M.op X3 X0) X1 X2
             have i₂ := b3e46 X3 X0
             grind)
          | exact superpose b3e46 b3e39
          | exact resolve b3e39 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e482 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X1 X2) (M.op X3 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e392 X0 X1 X2 X3 x
             have i₂ := b3e282 X0 X1 x y
             grind)
          | exact superpose b3e282 b3e392
          | exact resolve b3e392 b3e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e282 b3e392
        have b3e779 : ∀ X0 X2 : G, (M.op X0 (σ x)) ≠ X0 ∨ (k X0 (M.op X2 (σ y))) = X0 := by
          intro X0 X2
          first
          | (have i₁ := b3e49 X0 x (σ y) X2
             have i₂ := b3e40 X0 x
             grind)
          | exact superpose b3e40 b3e49
          | (have j0 := b3e49 X0 x (σ y) X2
             grind)
          | exact resolve b3e49 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e803 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e63 X0 x
             have i₂ := b3e247
             grind)
          | exact superpose b3e247 b3e63
          | exact resolve b3e63 b3e247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e2649 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b3e56 X0 X1 X2 (M.op X0 X1)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e2747 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 (M.op X1 X2))) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e2649 X0 x X2
             have i₂ := b3e12 X0 X1 X2 x
             grind)
          | exact superpose b3e12 b3e2649
          | exact resolve b3e2649 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2880 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X0 (M.op X1 X2)) X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e50 X0 X1 X2 (M.op X1 X2)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e2974 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e75 (k (τ X0) X1) X1
             have i₂ := b3e30 X0 X1
             grind)
          | exact superpose b3e30 b3e75
          | exact resolve b3e75 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2975 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e75 (k X1 (τ X0)) X1
             have i₂ := b3e31 X0 X1
             grind)
          | exact superpose b3e31 b3e75
          | exact resolve b3e75 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3001 : ∀ X0 X1 : G, (M.op y (σ X1)) = (M.op x (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e46 (σ X0) (σ X1)
             have i₂ := b3e75 X0 X1
             grind)
          | exact superpose b3e75 b3e46
          | (have j1 := b3e75 X0 X1
             grind)
          | exact resolve b3e46 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3014 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e75 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3015 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e75 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e3020 : ∀ X0 X1 : G, (M.op x (σ (k X0 X1))) = (M.op x (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e3001 X0 X1
             have i₂ := b3e803 (σ X1)
             grind)
          | exact superpose b3e803 b3e3001
          | (have j0 := b3e3001 X0 X1
             grind)
          | exact resolve b3e3001 b3e803
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3001
        have b3e3063 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e88 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e88
          | exact resolve b3e88 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3067 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e88 X2 (k X0 (τ X1))
             have i₂ := b3e31 X1 X0
             grind)
          | exact superpose b3e31 b3e88
          | exact resolve b3e88 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3068 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e88 X0 X1
             have i₂ := b3e17 X0 (σ X1)
             grind)
          | exact superpose b3e17 b3e88
          | (have j1 := b3e17 X0 (σ X1)
             grind)
          | exact resolve b3e88 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3109 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e99 (k (τ X0) X1) X2
             have i₂ := b3e30 X0 X1
             grind)
          | exact superpose b3e30 b3e99
          | exact resolve b3e99 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3155 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X0 X2) y) := by
          intro X0 X2
          first
          | (have i₁ := b3e12 X0 x y X2
             have i₂ := b3e283 X0 x
             grind)
          | exact superpose b3e283 b3e12
          | exact resolve b3e12 b3e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3503 : ∀ X0 : G, (k X0 (M.op X0 y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e2747 X0 x y
             have i₂ := b3e283 X0 x
             grind)
          | exact superpose b3e283 b3e2747
          | exact resolve b3e2747 b3e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2747
        have b3e3679 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) y))) := by
          intro X0
          first
          | (have i₁ := b3e99 X0 (M.op (σ X0) y)
             have i₂ := b3e3503 (σ X0)
             grind)
          | exact superpose b3e3503 b3e99
          | exact resolve b3e99 b3e3503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e3680 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) y))) := by
          intro X0
          first
          | (have i₁ := b3e30 X0 (M.op (τ X0) y)
             have i₂ := b3e3503 (τ X0)
             grind)
          | exact superpose b3e3503 b3e30
          | exact resolve b3e30 b3e3503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3503
        have b3e3683 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e3680 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e3680
          | exact resolve b3e3680 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3680
        have b3e3684 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e3679 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e3679
          | exact resolve b3e3679 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3679
        have b3e6523 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b3e482 x X1 x y
             have i₂ := b3e359
             grind)
          | exact superpose b3e359 b3e482
          | exact resolve b3e482 b3e359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e482
        have b3e10933 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e779 (σ x) X0
             have i₂ := b3e130
             grind)
          | exact superpose b3e130 b3e779
          | (have j0 := b3e779 (σ x) X0
             grind)
          | (have r₁ := b3e779 (σ x) x
             have r₂ := b3e130
             grind)
          | exact resolve b3e779 b3e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130 b3e779
        have b3e10937 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have j0 := b3e10933 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10933
        have b3e19416 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e85 (σ X0) X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e85
          | exact resolve b3e85 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e19476 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e19416 X0 X1
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e19416
          | (have j0 := b3e19416 X0 X1
             grind)
          | exact resolve b3e19416 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e19416
        have b3e20029 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e3014 y y
             have i₂ := b3e83
             grind)
          | exact superpose b3e83 b3e3014
          | (have j0 := b3e3014 y y
             grind)
          | exact resolve b3e3014 b3e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83 b3e3014
        have b3e20039 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e20029
        have b3e20040 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e20039
        have b3e20089 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e118 X0 (σ y)
             have i₂ := b3e20040
             grind)
          | exact superpose b3e20040 b3e118
          | exact resolve b3e118 b3e20040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e118
        have b3e20097 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e40 (σ y) (σ y)
             have i₂ := b3e20040
             grind)
          | exact superpose b3e20040 b3e40
          | exact resolve b3e40 b3e20040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e20165 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e20097
             have i₂ := b3e20040
             grind)
          | exact superpose b3e20040 b3e20097
          | exact resolve b3e20097 b3e20040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20040 b3e20097
        have b3e20193 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X2))) ≠ (σ (M.op X0 (M.op X1 X2))) ∨ (σ X2) = (M.op (σ (M.op X0 (M.op X1 X2))) (σ X2)) ∨ (σ (M.op X0 (M.op X1 X2))) = (M.op (σ (M.op X0 (M.op X1 X2))) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e3015 (M.op X0 (M.op X1 X2)) X2
             have i₂ := b3e2880 X0 X1 X2
             grind)
          | exact superpose b3e2880 b3e3015
          | (have j0 := b3e3015 (M.op X0 (M.op X1 X2)) X2
             grind)
          | exact resolve b3e3015 b3e2880
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2880 b3e3015
        have b3e20259 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X2))) = (M.op (σ (M.op X0 (M.op X1 X2))) (σ X2)) ∨ (σ X2) = (M.op (σ (M.op X0 (M.op X1 X2))) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e20193 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20193
        have b3e25450 : ∀ X0 X1 : G, (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op x (σ (σ X1))) = (M.op x (σ (σ (k X0 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e3020 (σ X0) (σ X1)
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e3020
          | (have j0 := b3e3020 (σ X0) (σ X1)
             grind)
          | exact resolve b3e3020 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3020
        have b3e43425 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X1)) = (M.op (k X0 (σ X1)) (σ (M.op (M.op (k (τ X0) X1) X2) X3))) ∨ (σ (M.op (M.op (k (τ X0) X1) X2) X3)) = (M.op (k X0 (σ X1)) (σ (M.op (M.op (k (τ X0) X1) X2) X3))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ (M.op (M.op (k (τ X0) X1) X2) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e2974 X0 X1 (M.op (M.op (k (τ X0) X1) X2) X3)
             have i₂ := b3e2649 (k (τ X0) X1) X2 X3
             grind)
          | exact superpose b3e2649 b3e2974
          | (have j0 := b3e2974 X0 X1 (M.op (M.op (k (τ X0) X1) X2) X3)
             grind)
          | exact resolve b3e2974 b3e2649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2974
        have b3e43573 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ (M.op (M.op (k (τ X0) X1) X2) X3))) ∨ (σ (M.op (M.op (k (τ X0) X1) X2) X3)) = (M.op (k X0 (σ X1)) (σ (M.op (M.op (k (τ X0) X1) X2) X3))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ (M.op (M.op (k (τ X0) X1) X2) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e43425 X0 X1 X2 X3
             have i₂ := b3e30 X0 X1
             grind)
          | exact superpose b3e30 b3e43425
          | (have j0 := b3e43425 X0 X1 X2 X3
             grind)
          | exact resolve b3e43425 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e43425
        have b3e43574 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op (k (τ X0) X1) X2) X3)) = (M.op (k X0 (σ X1)) (σ (M.op (M.op (k (τ X0) X1) X2) X3))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ (M.op (M.op (k (τ X0) X1) X2) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b3e43573 X0 X1 X2 X3
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43573
        have b3e43870 : ∀ X0 X1 X2 X3 : G, (σ (k X0 (τ X1))) = (M.op (k (σ X0) X1) (σ (M.op (M.op (k X0 (τ X1)) X2) X3))) ∨ (σ (M.op (M.op (k X0 (τ X1)) X2) X3)) = (M.op (k (σ X0) X1) (σ (M.op (M.op (k X0 (τ X1)) X2) X3))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (M.op (M.op (k X0 (τ X1)) X2) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e2975 X0 X1 (M.op (M.op (k X0 (τ X1)) X2) X3)
             have i₂ := b3e2649 (k X0 (τ X1)) X2 X3
             grind)
          | exact superpose b3e2649 b3e2975
          | (have j0 := b3e2975 X0 X1 (M.op (M.op (k X0 (τ X1)) X2) X3)
             grind)
          | exact resolve b3e2975 b3e2649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2975
        have b3e44022 : ∀ X0 X1 X2 X3 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (M.op (M.op (k X0 (τ X1)) X2) X3))) ∨ (σ (M.op (M.op (k X0 (τ X1)) X2) X3)) = (M.op (k (σ X0) X1) (σ (M.op (M.op (k X0 (τ X1)) X2) X3))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (M.op (M.op (k X0 (τ X1)) X2) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e43870 X0 X1 X2 X3
             have i₂ := b3e31 X1 X0
             grind)
          | exact superpose b3e31 b3e43870
          | (have j0 := b3e43870 X0 X1 X2 X3
             grind)
          | exact resolve b3e43870 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e43870
        have b3e44023 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op (k X0 (τ X1)) X2) X3)) = (M.op (k (σ X0) X1) (σ (M.op (M.op (k X0 (τ X1)) X2) X3))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ (M.op (M.op (k X0 (τ X1)) X2) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b3e44022 X0 X1 X2 X3
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44022
        have b3e48335 : ∀ X0 X1 X2 X3 : G, (τ (k (k X0 (k (σ X1) X2)) X3)) = (k (k (τ X0) (k X1 (τ X2))) (τ X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e3063 X3 (k X0 (k (σ X1) X2))
             have i₂ := b3e3067 X1 X2 X0
             grind)
          | exact superpose b3e3067 b3e3063
          | exact resolve b3e3063 b3e3067
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3067
        have b3e144577 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op X0 (M.op X1 y)))) ∨ (σ y) = (M.op (σ (M.op X0 (M.op X1 y))) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e10937 (σ (M.op X0 (M.op X1 y)))
             have i₂ := b3e20259 X0 X1 y
             grind)
          | exact superpose b3e20259 b3e10937
          | (have j1 := b3e20259 X0 X1 y
             grind)
          | exact resolve b3e10937 b3e20259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10937
        have b3e144840 : ∀ X0 X1 X2 : G, (σ X2) ≠ (σ (M.op X0 (M.op X1 X2))) ∨ (σ X2) = (M.op (σ (M.op X0 (M.op X1 X2))) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e20259 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20259
        have b3e144880 : ∀ X0 X1 : G, (σ x) = (σ (k x (M.op X0 (M.op X1 y)))) ∨ (σ y) = (M.op (σ (M.op X0 (M.op X1 y))) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e144577 X0 X1
             have i₂ := b3e18 x (M.op X0 (M.op X1 y))
             grind)
          | exact superpose b3e18 b3e144577
          | (have j0 := b3e144577 X0 X1
             grind)
          | exact resolve b3e144577 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144577
        have b3e145007 : ∀ X0 X1 : G, (σ x) = (σ (k x (M.op X0 y))) ∨ (σ y) = (M.op (σ (M.op X0 (M.op X1 y))) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e144880 X0 X1
             have i₂ := b3e283 X0 X1
             grind)
          | exact superpose b3e283 b3e144880
          | (have j0 := b3e144880 X0 X1
             grind)
          | exact resolve b3e144880 b3e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144880
        have b3e145127 : ∀ X0 X1 : G, (σ y) = (M.op (σ (M.op X0 (M.op X1 y))) (σ x)) ∨ (σ x) = (σ (k x (M.op X0 y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e145007 X0 X1
             have i₂ := b3e20089 (σ (M.op X0 (M.op X1 y)))
             grind)
          | exact superpose b3e20089 b3e145007
          | (have j0 := b3e145007 X0 X1
             grind)
          | exact resolve b3e145007 b3e20089
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e145007
        have b3e145218 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ x)) ∨ (σ x) = (σ (k x (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b3e145127 X0 x
             have i₂ := b3e283 X0 x
             grind)
          | exact superpose b3e283 b3e145127
          | (have j0 := b3e145127 X0 x
             grind)
          | exact resolve b3e145127 b3e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e283 b3e145127
        have b3e155776 : ∀ X0 : G, (σ x) = (σ (k x (M.op X0 y))) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e3155 (σ (M.op X0 y)) (σ x)
             have i₂ := b3e145218 X0
             grind)
          | exact superpose b3e145218 b3e3155
          | (have j1 := b3e145218 X0
             grind)
          | exact resolve b3e3155 b3e145218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3155 b3e145218
        have b3e209774 : ∀ X0 : G, (σ x) = (σ (M.op x (M.op X0 y))) ∨ (M.op X0 y) = (M.op x (M.op X0 y)) ∨ x = (M.op x (M.op X0 y)) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e19476 x (M.op X0 y)
             have i₂ := b3e155776 X0
             grind)
          | exact superpose b3e155776 b3e19476
          | (have j0 := b3e19476 x (M.op X0 y)
             have j1 := b3e155776 X0
             grind)
          | exact resolve b3e19476 b3e155776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e19476 b3e155776
        have b3e209949 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (M.op X0 y) = (M.op x (M.op X0 y)) ∨ x = (M.op x (M.op X0 y)) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e209774 X0
             have i₂ := b3e46 X0 y
             grind)
          | exact superpose b3e46 b3e209774
          | (have j0 := b3e209774 X0
             grind)
          | exact resolve b3e209774 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209774
        have b3e209971 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 y) = (M.op x (M.op X0 y)) ∨ x = (M.op x (M.op X0 y)) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e209949 X0
             have i₂ := b3e70
             grind)
          | exact superpose b3e70 b3e209949
          | (have j0 := b3e209949 X0
             grind)
          | exact resolve b3e209949 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209949
        have b3e209989 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 y)) ∨ x = (M.op x (M.op X0 y)) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have j0 := b3e209971 X0
             grind)
          | (have r₁ := b3e209971 X0
             have r₂ := b3e25
             grind)
          | exact resolve b3e209971 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209971
        have b3e209996 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ x = (M.op x (M.op X0 y)) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e209989 X0
             have i₂ := b3e46 X0 y
             grind)
          | exact superpose b3e46 b3e209989
          | (have j0 := b3e209989 X0
             grind)
          | exact resolve b3e209989 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209989
        have b3e210003 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x (M.op X0 y)) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e209996 X0
             have i₂ := b3e70
             grind)
          | exact superpose b3e70 b3e209996
          | (have j0 := b3e209996 X0
             grind)
          | exact resolve b3e209996 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209996
        have b3e210006 : ∀ X0 : G, x = (M.op y y) ∨ y = (M.op X0 y) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e210003 X0
             have i₂ := b3e46 X0 y
             grind)
          | exact superpose b3e46 b3e210003
          | (have j0 := b3e210003 X0
             grind)
          | exact resolve b3e210003 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e210003
        have b3e210009 : ∀ X0 : G, x = y ∨ y = (M.op X0 y) ∨ (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e210006 X0
             have i₂ := b3e70
             grind)
          | exact superpose b3e70 b3e210006
          | (have j0 := b3e210006 X0
             grind)
          | exact resolve b3e210006 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70 b3e210006
        have b3e210012 : ∀ X0 : G, (M.op (σ y) y) = (M.op (σ (M.op X0 y)) y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b3e210009 X0
             grind)
          | (have r₁ := b3e210009 X0
             have r₂ := b3e23
             grind)
          | exact resolve b3e210009 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e210009
        have b3e210762 : ∀ X0 : G, (M.op (σ (M.op X0 y)) (σ x)) = (M.op (M.op (σ y) y) (σ x)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e131 (σ (M.op X0 y)) y
             have i₂ := b3e210012 X0
             grind)
          | exact superpose b3e210012 b3e131
          | (have j1 := b3e210012 X0
             grind)
          | exact resolve b3e131 b3e210012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e210012
        have b3e211074 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ x)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e210762 X0
             have i₂ := b3e131 (σ y) y
             grind)
          | exact superpose b3e131 b3e210762
          | (have j0 := b3e210762 X0
             grind)
          | exact resolve b3e210762 b3e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e210762
        have b3e211130 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ x)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e211074 X0
             have i₂ := b3e20165
             grind)
          | exact superpose b3e20165 b3e211074
          | (have j0 := b3e211074 X0
             grind)
          | exact resolve b3e211074 b3e20165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20165 b3e211074
        have b3e215193 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ (M.op X0 y))) x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op X0 y)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e3068 (σ (M.op X0 y)) x
             have i₂ := b3e211130 X0
             grind)
          | exact superpose b3e211130 b3e3068
          | (have j1 := b3e211130 X0
             grind)
          | exact resolve b3e3068 b3e211130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3068 b3e211130
        have b3e215611 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ (M.op X0 y))) x) ∨ (σ y) = (σ (M.op X0 y)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b3e215193 X0
             grind)
          | (have r₁ := b3e215193 X0
             have r₂ := b3e25
             grind)
          | exact resolve b3e215193 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e215193
        have b3e215686 : ∀ X0 : G, (τ (σ y)) = (k (M.op X0 y) x) ∨ (σ y) = (σ (M.op X0 y)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e215611 X0
             have i₂ := b3e13 (M.op X0 y)
             grind)
          | exact superpose b3e13 b3e215611
          | (have j0 := b3e215611 X0
             grind)
          | exact resolve b3e215611 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e215611
        have b3e215727 : ∀ X0 : G, y = (k (M.op X0 y) x) ∨ (σ y) = (σ (M.op X0 y)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e215686 X0
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e215686
          | (have j0 := b3e215686 X0
             grind)
          | exact resolve b3e215686 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e215686
        have b3e307349 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 (σ (σ X1)) (σ (σ X0))
             have i₂ := b3e25450 X1 X0
             grind)
          | exact superpose b3e25450 b3e15
          | (have j0 := b3e15 (σ (σ X1)) (σ (σ X0))
             have j1 := b3e25450 X1 X0
             grind)
          | (have r₁ := b3e15 (σ (σ X1)) (σ (σ X1))
             have r₂ := b3e25450 X1 X1
             grind)
          | (have r₁ := b3e15 (σ (σ X0)) (σ (σ X1))
             have r₂ := b3e25450 X0 X1
             grind)
          | exact resolve b3e15 b3e25450
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e307350 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 (σ (σ X0)) (σ (σ X1))
             have i₂ := b3e25450 X0 X1
             grind)
          | exact superpose b3e25450 b3e16
          | (have j0 := b3e16 (σ (σ X1)) (σ (σ X0))
             have j1 := b3e25450 X1 X0
             grind)
          | (have r₁ := b3e16 (σ (σ X0)) (σ (σ X1))
             have r₂ := b3e25450 X0 X1
             grind)
          | (have r₁ := b3e16 (σ (σ X0)) (σ (σ X0))
             have r₂ := b3e25450 X0 X0
             grind)
          | exact resolve b3e16 b3e25450
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25450
        have b3e308070 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have j0 := b3e307350 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e307350
        have b3e308160 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have j0 := b3e308070 X0 X1
             have j1 := b3e15 (σ (σ X1)) (σ (σ X0))
             grind)
          | (have r₁ := b3e308070 X0 X1
             have r₂ := b3e15 (σ (σ X1)) (σ (σ X0))
             grind)
          | exact resolve b3e308070 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308070
        have b3e308161 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have j0 := b3e307349 X0 X1
             have j1 := b3e15 (σ (σ X1)) (σ (σ X0))
             grind)
          | (have r₁ := b3e307349 X0 X1
             have r₂ := b3e15 (σ (σ X1)) (σ (σ X0))
             grind)
          | exact resolve b3e307349 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e307349
        have b3e308243 : ∀ X0 X1 : G, (σ (σ X1)) = (σ (k (σ X1) (σ X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e308160 X0 X1
             have i₂ := b3e18 (σ X1) (σ X0)
             grind)
          | exact superpose b3e18 b3e308160
          | (have j0 := b3e308160 X0 X1
             grind)
          | exact resolve b3e308160 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308160
        have b3e308244 : ∀ X0 X1 : G, (σ (σ X1)) = (σ (k (σ X1) (σ X0))) ∨ (σ (σ X0)) ≠ (σ (σ X1)) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e308161 X0 X1
             have i₂ := b3e18 (σ X1) (σ X0)
             grind)
          | exact superpose b3e18 b3e308161
          | (have j0 := b3e308161 X0 X1
             grind)
          | exact resolve b3e308161 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308161
        have b3e308278 : ∀ X0 X1 : G, (σ (σ X1)) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e308243 X0 X1
             have i₂ := b3e18 X1 X0
             grind)
          | exact superpose b3e18 b3e308243
          | (have j0 := b3e308243 X0 X1
             grind)
          | exact resolve b3e308243 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308243
        have b3e308279 : ∀ X0 X1 : G, (σ (σ X1)) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) ≠ (σ (σ X1)) ∨ (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e308244 X0 X1
             have i₂ := b3e18 X1 X0
             grind)
          | exact superpose b3e18 b3e308244
          | (have j0 := b3e308244 X0 X1
             grind)
          | exact resolve b3e308244 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308244
        have b3e308284 : ∀ X0 X1 : G, (M.op x (σ (σ X0))) = (M.op x (σ (σ (k X1 X0)))) ∨ (σ (σ X1)) = (σ (σ (k X1 X0))) := by
          intro X0 X1
          first
          | (have j0 := b3e308279 X0 X1
             have j1 := b3e308278 X0 X1
             grind)
          | (have r₁ := b3e308279 X1 (k X1 X0)
             have r₂ := b3e308278 X0 X1
             grind)
          | (have r₁ := b3e308279 (k X1 X0) X1
             have r₂ := b3e308278 X0 X1
             grind)
          | (have r₁ := b3e308279 X0 X1
             have r₂ := b3e308278 X0 X1
             grind)
          | exact resolve b3e308279 b3e308278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308278 b3e308279
        have b3e1315048 : ∀ X0 X1 : G, (M.op x (σ (σ (τ X1)))) = (M.op x (σ (σ (τ (k X0 X1))))) ∨ (σ (σ (τ X0))) = (σ (σ (τ (k X0 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e308284 (τ X0) (τ X1)
             have i₂ := b3e3063 X0 X1
             grind)
          | exact superpose b3e3063 b3e308284
          | exact resolve b3e308284 b3e3063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308284
        have b3e1315287 : ∀ X0 X1 : G, (M.op x (σ (k X0 X1))) = (M.op x (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ (k X0 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1315048 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e1315048
          | (have j0 := b3e1315048 X0 X1
             grind)
          | exact resolve b3e1315048 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1315048
        have b3e1315293 : ∀ X0 X1 : G, (M.op x (σ (k X0 X1))) = (M.op x (σ X1)) ∨ (σ (σ (τ X0))) = (σ (σ (τ (k X0 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1315287 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e1315287
          | (have j0 := b3e1315287 X0 X1
             grind)
          | exact resolve b3e1315287 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1315287
        have b3e1315297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (σ (τ X0))) ∨ (M.op x (σ (k X0 X1))) = (M.op x (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1315293 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e1315293
          | (have j0 := b3e1315293 X0 X1
             grind)
          | exact resolve b3e1315293 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1315293
        have b3e1315298 : ∀ X0 X1 : G, (M.op x (σ (k X0 X1))) = (M.op x (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1315297 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1315297
          | (have j0 := b3e1315297 X0 X1
             grind)
          | exact resolve b3e1315297 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1315297
        have b3e1317520 : ∀ X0 X1 : G, (M.op x (σ (τ X1))) = (M.op x (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1315298 (τ X1) (τ X0)
             have i₂ := b3e3063 X0 X1
             grind)
          | exact superpose b3e3063 b3e1315298
          | exact resolve b3e1315298 b3e3063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1315298
        have b3e1317914 : ∀ X0 X1 : G, (M.op x (σ (τ X1))) = (M.op x (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1317520 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e1317520
          | (have j0 := b3e1317520 X0 X1
             grind)
          | exact resolve b3e1317520 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1317520
        have b3e1317939 : ∀ X0 X1 : G, (M.op x X1) = (M.op x (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1317914 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e1317914
          | (have j0 := b3e1317914 X0 X1
             grind)
          | exact resolve b3e1317914 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1317914
        have b3e1317955 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op x X1) = (M.op x (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1317939 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e1317939
          | (have j0 := b3e1317939 X0 X1
             grind)
          | exact resolve b3e1317939 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1317939
        have b3e1317968 : ∀ X0 X1 : G, (M.op x X1) = (M.op x (k X0 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1317955 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1317955
          | (have j0 := b3e1317955 X0 X1
             grind)
          | exact resolve b3e1317955 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1317955
        have b3e1322200 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ y = (M.op X0 y) ∨ (σ y) = (σ (M.op X0 y)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e1317968 (M.op X0 y) x
             have i₂ := b3e215727 X0
             grind)
          | exact superpose b3e215727 b3e1317968
          | (have j1 := b3e215727 X0
             grind)
          | exact resolve b3e1317968 b3e215727
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e215727 b3e1317968
        have b3e1322638 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ y = (M.op X0 y) ∨ (σ y) = (σ (M.op X0 y)) := by
          intro X0
          first
          | (have j0 := b3e1322200 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1322200
        have b3e1322689 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op X0 y) ∨ (σ y) = (σ (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e1322638 X0
             have i₂ := b3e247
             grind)
          | exact superpose b3e247 b3e1322638
          | (have j0 := b3e1322638 X0
             grind)
          | exact resolve b3e1322638 b3e247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e247 b3e1322638
        have b3e1322700 : ∀ X0 : G, x = y ∨ y = (M.op X0 y) ∨ (σ y) = (σ (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e1322689 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1322689
          | (have j0 := b3e1322689 X0
             grind)
          | exact resolve b3e1322689 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1322689
        have b3e1322708 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b3e1322700 X0
             grind)
          | (have r₁ := b3e1322700 X0
             have r₂ := b3e23
             grind)
          | exact resolve b3e1322700 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e1322700
        have b3e1323765 : ∀ X0 : G, (M.op X0 y) = (τ (σ y)) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (M.op X0 y)
             have i₂ := b3e1322708 X0
             grind)
          | exact superpose b3e1322708 b3e13
          | (have j1 := b3e1322708 X0
             grind)
          | exact resolve b3e13 b3e1322708
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1322708
        have b3e1324011 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e1323765 X0
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1323765
          | (have j0 := b3e1323765 X0
             grind)
          | exact resolve b3e1323765 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1323765
        have b3e1324012 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b3e1324011 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1324011
        have b3e1325059 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op y (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e131 X0 y
             have i₂ := b3e1324012 X0
             grind)
          | exact superpose b3e1324012 b3e131
          | exact resolve b3e131 b3e1324012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e131
        have b3e1325179 : ∀ X0 : G, (M.op y x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e6523 X0 y
             have i₂ := b3e1324012 X0
             grind)
          | exact superpose b3e1324012 b3e6523
          | exact resolve b3e6523 b3e1324012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6523
        have b3e1325325 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 y)) ∨ (σ y) = (M.op (σ (M.op X0 y)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e144840 X0 X0 y
             have i₂ := b3e1324012 X0
             grind)
          | exact superpose b3e1324012 b3e144840
          | exact resolve b3e144840 b3e1324012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144840
        have b3e1325407 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e2649 X0 x y
             have i₂ := b3e1324012 (M.op X0 x)
             grind)
          | exact superpose b3e1324012 b3e2649
          | exact resolve b3e2649 b3e1324012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2649
        have b3e1325577 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e3684 X0
             have i₂ := b3e1324012 (σ X0)
             grind)
          | exact superpose b3e1324012 b3e3684
          | exact resolve b3e3684 b3e1324012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3684
        have b3e1325797 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e3683 X0
             have i₂ := b3e1324012 (τ X0)
             grind)
          | exact superpose b3e1324012 b3e3683
          | exact resolve b3e3683 b3e1324012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3683
        have b3e1326181 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op X0 y)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e1325325 X0
             have i₂ := b3e1324012 X0
             grind)
          | exact superpose b3e1324012 b3e1325325
          | (have j0 := b3e1325325 X0
             grind)
          | exact resolve b3e1325325 b3e1324012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1324012 b3e1325325
        have b3e1326182 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ y)) := by
          intro X0
          first
          | (have j0 := b3e1326181 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1326181
        have b3e1326238 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e1325179 X0
             have i₂ := b3e359
             grind)
          | exact superpose b3e359 b3e1325179
          | exact resolve b3e1325179 b3e359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e359 b3e1325179
        have b3e1326281 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op x (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e1325059 X0
             have i₂ := b3e803 (σ x)
             grind)
          | exact superpose b3e803 b3e1325059
          | exact resolve b3e1325059 b3e803
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e803 b3e1325059
        have b3e1326376 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e1326182 X0
             have i₂ := b3e20089 (σ (M.op X0 y))
             grind)
          | exact superpose b3e20089 b3e1326182
          | exact resolve b3e1326182 b3e20089
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20089 b3e1326182
        have b3e1326476 : (σ y) = (M.op x (σ x)) := by
          first
          | (have i₁ := b3e1326376 x
             have i₂ := b3e1326281 (σ (M.op x y))
             grind)
          | exact superpose b3e1326281 b3e1326376
          | exact resolve b3e1326376 b3e1326281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1326376
        have b3e1329161 : ∀ X0 X1 : G, (σ x) = (M.op (k (σ X0) X1) (σ x)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e44023 X0 X1 x x
             have i₂ := b3e1326238 (M.op (k X0 (τ X1)) x)
             grind)
          | exact superpose b3e1326238 b3e44023
          | exact resolve b3e44023 b3e1326238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44023
        have b3e1329164 : ∀ X0 X1 : G, (σ x) = (M.op (k X0 (σ X1)) (σ x)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e43574 X0 X1 x x
             have i₂ := b3e1326238 (M.op (k (τ X0) X1) x)
             grind)
          | exact superpose b3e1326238 b3e43574
          | exact resolve b3e43574 b3e1326238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43574 b3e1326238
        have b3e1329644 : ∀ X0 X1 : G, (σ x) = (M.op x (σ x)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1329164 X0 X1
             have i₂ := b3e1326281 (k X0 (σ X1))
             grind)
          | exact superpose b3e1326281 b3e1329164
          | (have j0 := b3e1329164 X0 X1
             grind)
          | exact resolve b3e1329164 b3e1326281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329164
        have b3e1329646 : ∀ X0 X1 : G, (σ x) = (M.op x (σ x)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1329161 X0 X1
             have i₂ := b3e1326281 (k (σ X0) X1)
             grind)
          | exact superpose b3e1326281 b3e1329161
          | (have j0 := b3e1329161 X0 X1
             grind)
          | exact resolve b3e1329161 b3e1326281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329161
        have b3e1329849 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1329644 X0 X1
             have i₂ := b3e1326476
             grind)
          | exact superpose b3e1326476 b3e1329644
          | (have j0 := b3e1329644 X0 X1
             grind)
          | exact resolve b3e1329644 b3e1326476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329644
        have b3e1329850 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1329646 X0 X1
             have i₂ := b3e1326476
             grind)
          | exact superpose b3e1326476 b3e1329646
          | (have j0 := b3e1329646 X0 X1
             grind)
          | exact resolve b3e1329646 b3e1326476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329646
        have b3e1329912 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ x)) := by
          intro X0 X1
          first
          | (have j0 := b3e1329849 X0 X1
             grind)
          | (have r₁ := b3e1329849 X0 X1
             have r₂ := b3e25
             grind)
          | exact resolve b3e1329849 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329849
        have b3e1329913 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ x)) := by
          intro X0 X1
          first
          | (have j0 := b3e1329850 X0 X1
             grind)
          | (have r₁ := b3e1329850 X0 X1
             have r₂ := b3e25
             grind)
          | exact resolve b3e1329850 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329850
        have b3e1329943 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op x (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1329912 X0 X1
             have i₂ := b3e1326281 (k X0 (σ X1))
             grind)
          | exact superpose b3e1326281 b3e1329912
          | exact resolve b3e1329912 b3e1326281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329912
        have b3e1329944 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op x (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1329913 X0 X1
             have i₂ := b3e1326281 (k (σ X0) X1)
             grind)
          | exact superpose b3e1326281 b3e1329913
          | exact resolve b3e1329913 b3e1326281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1326281 b3e1329913
        have b3e1329966 : ∀ X0 X1 : G, (σ y) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1329943 X0 X1
             have i₂ := b3e1326476
             grind)
          | exact superpose b3e1326476 b3e1329943
          | exact resolve b3e1329943 b3e1326476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329943
        have b3e1329967 : ∀ X0 X1 : G, (σ y) = (k (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e1329944 X0 X1
             have i₂ := b3e1326476
             grind)
          | exact superpose b3e1326476 b3e1329944
          | exact resolve b3e1329944 b3e1326476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1326476 b3e1329944
        have b3e1331823 : ∀ X0 X1 X2 : G, (k (k (τ X1) X0) (τ X2)) = (τ (k (k X1 (k (σ X0) y)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e48335 X1 X0 y X2
             have i₂ := b3e1325577 X0
             grind)
          | exact superpose b3e1325577 b3e48335
          | exact resolve b3e48335 b3e1325577
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48335 b3e1325577
        have b3e1332191 : ∀ X0 X1 X2 : G, (k (k (τ X1) X0) (τ X2)) = (τ (k (k X1 (σ y)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1331823 X0 X1 X2
             have i₂ := b3e1329967 X0 y
             grind)
          | exact superpose b3e1329967 b3e1331823
          | exact resolve b3e1331823 b3e1329967
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329967 b3e1331823
        have b3e1332302 : ∀ X0 X1 X2 : G, (k (k (τ X1) X0) (τ X2)) = (k (k (τ X1) y) (τ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1332191 X0 X1 X2
             have i₂ := b3e3109 X1 y X2
             grind)
          | exact superpose b3e3109 b3e1332191
          | exact resolve b3e1332191 b3e3109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1332191
        have b3e1332342 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X2)) = (k (k (τ X1) X0) (τ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1332302 X0 X1 X2
             have i₂ := b3e1325407 (τ X1)
             grind)
          | exact superpose b3e1325407 b3e1332302
          | exact resolve b3e1332302 b3e1325407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1332302
        have b3e1332367 : ∀ X0 X1 X2 : G, (k (k (τ X1) X0) (τ X2)) = (τ (k X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e1332342 X0 X1 X2
             have i₂ := b3e3063 X2 X1
             grind)
          | exact superpose b3e3063 b3e1332342
          | exact resolve b3e1332342 b3e3063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3063 b3e1332342
        have b3e1342911 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (k (k (τ X0) X1) (τ (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e3109 X0 X1 (σ y)
             have i₂ := b3e1325797 (k X0 (σ X1))
             grind)
          | exact superpose b3e1325797 b3e3109
          | exact resolve b3e3109 b3e1325797
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3109 b3e1325797
        have b3e1342970 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (τ (k X0 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1342911 X0 X1
             have i₂ := b3e1332367 X1 X0 (σ y)
             grind)
          | exact superpose b3e1332367 b3e1342911
          | exact resolve b3e1342911 b3e1332367
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1332367 b3e1342911
        have b3e1343134 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (k (τ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e1342970 X0 X1
             have i₂ := b3e88 X0 y
             grind)
          | exact superpose b3e88 b3e1342970
          | exact resolve b3e1342970 b3e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88 b3e1342970
        have b3e1343264 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1343134 X0 X1
             have i₂ := b3e1325407 (τ X0)
             grind)
          | exact superpose b3e1325407 b3e1343134
          | exact resolve b3e1343134 b3e1325407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1325407 b3e1343134
        have b3e1343313 : ∀ X0 : G, (τ X0) = (τ (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e1343264 X0 x
             have i₂ := b3e1329966 X0 x
             grind)
          | exact superpose b3e1329966 b3e1343264
          | exact resolve b3e1343264 b3e1329966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1329966 b3e1343264
        have b3e1343332 : ∀ X0 : G, (τ X0) = y := by
          intro X0
          first
          | (have i₁ := b3e1343313 X0
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1343313
          | exact resolve b3e1343313 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1343313
        have b3e1345232 : ∀ X0 : G, y = X0 := by
          intro X0
          first
          | (have i₁ := b3e13 X0
             have i₂ := b3e1343332 (σ X0)
             grind)
          | exact superpose b3e1343332 b3e13
          | exact resolve b3e13 b3e1343332
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1343332
        have b3e1353413 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e1345232 (k x y)
             grind)
          | exact superpose b3e1345232 b3e29
          | exact resolve b3e29 b3e1345232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e1345232
        have b3e1353487 : False := by grind
        exact b3e1353487
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (σ y) ≠ (σ y) := by
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e58 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e62 : x = y ∨ x = (k x y) := by grind
          clear b5e58
          have b5e66 : x = (k x y) := by
            first
            | (have r₁ := b5e62
               have r₂ := b5e25
               grind)
            | exact resolve b5e62 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e62
          have b5e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e2113 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e69 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e42304 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e2113 x y
               have i₂ := b5e66
               grind)
            | exact superpose b5e66 b5e2113
            | (have j0 := b5e2113 x y
               grind)
            | exact resolve b5e2113 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e2113
          have b5e42316 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e42304
          have b5e42374 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e42316
               have r₂ := b5e24
               grind)
            | exact resolve b5e42316 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42316
          have b5e42392 : False := by grind
          exact b5e42392
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b6e59 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e61 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e59
        have b6e64 : y = (M.op x y) := by
          first
          | (have r₁ := b6e61
             have r₂ := b6e20
             grind)
          | exact resolve b6e61 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e67 : False := by grind
        exact b6e67
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
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
          have b7e46 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e49 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e46
          have b7e52 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e49
               have r₂ := b7e25
               grind)
            | exact resolve b7e49 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e49
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
          have b7e67 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
          have b7e68 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e67
          have b7e70 : y = (M.op x y) := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e21
               grind)
            | exact resolve b7e68 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e72 : False := by grind
          exact b7e72
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e1984 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e54 x y
               grind)
            | exact superpose b8e54 b8e20
            | (have j1 := b8e54 x y
               grind)
            | exact resolve b8e20 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e2028 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1984
               have r₂ := b8e24
               grind)
            | exact resolve b8e1984 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1984
          have b8e2031 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e2028
               have r₂ := b8e23
               grind)
            | exact resolve b8e2028 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2028
          have b8e2032 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e2031
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2031
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e2031 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2031
          have b8e2033 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e2032
          have b8e2034 : x = (M.op x y) := by
            first
            | (have r₁ := b8e2033
               have r₂ := b8e22
               grind)
            | exact resolve b8e2033 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2033
          have b8e2035 : False := by grind
          exact b8e2035

/-- `Equation4559`: `x ◇ (y ◇ z) = (w ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxy_pxx_pxy_Equation4559 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4559 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4559.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b0e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e53 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e55 : (M.op x x) = (k x y) := by grind
      clear b0e53
      have b0e56 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e52
      have b0e57 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e56
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e56
        | exact resolve b0e56 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e58 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e57
           have i₂ := b0e55
           grind)
        | exact superpose b0e55 b0e57
        | exact resolve b0e57 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55 b0e57
      have b0e59 : False := by grind
      exact b0e59
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
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
        have b1e25 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e24
          | exact resolve b1e24 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e30 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ y)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (σ x) (σ y) X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X1) X2) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b1e12 X1 x X2 X4
             have i₂ := b1e12 X1 x X2 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ y) X0 X1 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op x x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X0 X1 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e49 (σ X0)
             grind)
          | exact superpose b1e49 b1e18
          | exact resolve b1e18 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e52 X0
             have i₂ := b1e49 X0
             grind)
          | exact superpose b1e49 b1e52
          | exact resolve b1e52 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e52
        have b1e121 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (σ y) x
             have i₂ := b1e30 X0 x
             grind)
          | exact superpose b1e30 b1e12
          | exact resolve b1e12 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e158 : ∀ X0 X1 : G, (M.op (M.op x x) X1) = (M.op (M.op X0 y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e31 X0 y X1 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e31
          | exact resolve b1e31 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e210 : (M.op (σ y) y) = (M.op (σ y) (M.op x x)) := by
          first
          | (have i₁ := b1e35 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e35
          | exact resolve b1e35 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e215 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 X3)) = (M.op (M.op (σ y) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X1 X0) X2 X3 (σ y)
             have i₂ := b1e35 X1 X0
             grind)
          | exact superpose b1e35 b1e12
          | exact resolve b1e12 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e223 : (M.op (σ y) y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b1e210
             have i₂ := b1e35 x x
             grind)
          | exact superpose b1e35 b1e210
          | exact resolve b1e210 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e210
        have b1e228 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op X0 (M.op (σ y) x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (σ y) y X1
             have i₂ := b1e223
             grind)
          | exact superpose b1e223 b1e12
          | exact resolve b1e12 b1e223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e268 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op x (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 x X2 X1 x
             have i₂ := b1e36 X0 X1
             grind)
          | exact superpose b1e36 b1e12
          | exact resolve b1e12 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e304 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (M.op (σ (M.op X0 X0)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e30 (σ X0) (σ X0)
             have i₂ := b1e55 X0
             grind)
          | exact superpose b1e55 b1e30
          | exact resolve b1e30 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e1606 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b1e121 X0 (σ y)
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e121
          | exact resolve b1e121 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121
        have b1e2439 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) X1) = (M.op (M.op X2 x) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e31 x x X1 X2
             have i₂ := b1e158 X0 X1
             grind)
          | exact superpose b1e158 b1e31
          | exact resolve b1e31 b1e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e3310 : ∀ X0 : G, (M.op y (M.op (σ y) x)) = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e268 (σ y) y X0
             have i₂ := b1e223
             grind)
          | exact superpose b1e223 b1e268
          | exact resolve b1e268 b1e223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e223 b1e268
        have b1e3503 : ∀ X0 : G, (M.op (M.op x x) x) = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e3310 X0
             have i₂ := b1e36 (σ y) x
             grind)
          | exact superpose b1e36 b1e3310
          | exact resolve b1e3310 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3310
        have b1e5018 : (M.op (σ (M.op y y)) (σ y)) = (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b1e55 (M.op y y)
             have i₂ := b1e1606 (σ (M.op y y))
             grind)
          | exact superpose b1e1606 b1e55
          | exact resolve b1e55 b1e1606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1606
        have b1e5021 : (M.op (σ (M.op y y)) (σ y)) = (σ (M.op (M.op (σ y) y) y)) := by
          first
          | (have i₁ := b1e5018
             have i₂ := b1e215 y y y y
             grind)
          | exact superpose b1e215 b1e5018
          | exact resolve b1e5018 b1e215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5018
        have b1e5076 : (M.op (σ (M.op y y)) (σ y)) = (σ (M.op y (M.op (σ y) x))) := by
          first
          | (have i₁ := b1e5021
             have i₂ := b1e228 y (σ y)
             grind)
          | exact superpose b1e228 b1e5021
          | exact resolve b1e5021 b1e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e228 b1e5021
        have b1e5095 : (M.op (σ (M.op y y)) (σ y)) = (σ (M.op (M.op x x) x)) := by
          first
          | (have i₁ := b1e5076
             have i₂ := b1e36 (σ y) x
             grind)
          | exact superpose b1e36 b1e5076
          | exact resolve b1e5076 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e5076
        have b1e5111 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) x)) := by
          first
          | (have i₁ := b1e5095
             have i₂ := b1e304 y
             grind)
          | exact superpose b1e304 b1e5095
          | exact resolve b1e5095 b1e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5095
        have b1e5123 : (σ (M.op y y)) = (σ (M.op (M.op x x) x)) := by
          first
          | (have i₁ := b1e5111
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e5111
          | exact resolve b1e5111 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5111
        have b1e14025 : ∀ X0 : G, (σ (M.op y y)) = (σ (M.op x (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e5123
             have i₂ := b1e3503 X0
             grind)
          | exact superpose b1e3503 b1e5123
          | exact resolve b1e5123 b1e3503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3503
        have b1e14029 : ∀ X0 : G, (σ (M.op y y)) = (σ (M.op (M.op X0 y) x)) := by
          intro X0
          first
          | (have i₁ := b1e5123
             have i₂ := b1e2439 X0 x x
             grind)
          | exact superpose b1e2439 b1e5123
          | exact resolve b1e5123 b1e2439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2439 b1e5123
        have b1e87055 : ∀ X0 : G, (M.op (σ (M.op (M.op X0 y) (M.op x x))) (σ y)) = (M.op (σ (M.op x x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e304 (M.op x x)
             have i₂ := b1e158 X0 (M.op x x)
             grind)
          | exact superpose b1e158 b1e304
          | exact resolve b1e304 b1e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e158
        have b1e87224 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op X0 y) (M.op x x))) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e87055 X0
             have i₂ := b1e304 x
             grind)
          | exact superpose b1e304 b1e87055
          | exact resolve b1e87055 b1e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87055
        have b1e87298 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op (σ y) y) x)) (σ y)) := by
          first
          | (have i₁ := b1e87224 x
             have i₂ := b1e215 y x x x
             grind)
          | exact superpose b1e215 b1e87224
          | exact resolve b1e87224 b1e215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e215 b1e87224
        have b1e87341 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y y)) (σ y)) := by
          first
          | (have i₁ := b1e87298
             have i₂ := b1e14029 (σ y)
             grind)
          | exact superpose b1e14029 b1e87298
          | exact resolve b1e87298 b1e14029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14029 b1e87298
        have b1e87365 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e87341
             have i₂ := b1e304 y
             grind)
          | exact superpose b1e304 b1e87341
          | exact resolve b1e87341 b1e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304 b1e87341
        have b1e87386 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e87365
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e87365
          | exact resolve b1e87365 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e87365
        have b1e87395 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e87386
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e87386
          | exact resolve b1e87386 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87386
        have b1e89215 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e87395
             grind)
          | exact superpose b1e87395 b1e13
          | exact resolve b1e13 b1e87395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87395
        have b1e89252 : y = (M.op y y) := by
          first
          | (have i₁ := b1e89215
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e89215
          | exact resolve b1e89215 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89215
        have b1e91105 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e14025 y
             have i₂ := b1e89252
             grind)
          | exact superpose b1e89252 b1e14025
          | exact resolve b1e14025 b1e89252
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14025 b1e89252
        have b1e91212 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e91105
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e91105
          | exact resolve b1e91105 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91105
        have b1e91224 : False := by grind
        exact b1e91224
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e57 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : (M.op x x) = (k x y) := by grind
        clear b2e57
        have b2e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e60 (σ X0)
             grind)
          | exact superpose b2e60 b2e18
          | exact resolve b2e18 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e63 X0
             have i₂ := b2e60 X0
             grind)
          | exact superpose b2e60 b2e63
          | exact resolve b2e63 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60 b2e63
        have b2e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e87 X0 X1
             have i₂ := b2e70 X0
             grind)
          | exact superpose b2e70 b2e87
          | (have j0 := b2e87 X0 X1
             grind)
          | exact resolve b2e87 b2e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e9187 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e109 x y
             grind)
          | exact superpose b2e109 b2e21
          | (have j1 := b2e109 x y
             grind)
          | exact resolve b2e21 b2e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109
        have b2e9319 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e9187
             have r₂ := b2e23
             grind)
          | exact resolve b2e9187 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e9187
        have b2e9349 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e9319
             have r₂ := b2e22
             grind)
          | exact resolve b2e9319 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9319
        have b2e9355 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e9349
             have i₂ := b2e61
             grind)
          | exact superpose b2e61 b2e9349
          | exact resolve b2e9349 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61 b2e9349
        have b2e9357 : False := by grind
        exact b2e9357
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : y ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by
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
        have b3e34 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X1) X2) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b3e12 X1 x X2 X4
             have i₂ := b3e12 X1 x X2 X0
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 y X0 X1 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op X0 (M.op X1 X2)) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e12 X2 X3 X4 (M.op x X0)
             have i₂ := b3e12 X0 X1 X2 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 X1 X2 x
             have i₂ := b3e12 X0 X3 X2 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : (M.op y (σ y)) = (M.op y (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b3e36 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e36
          | exact resolve b3e36 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (M.op (σ x) (σ x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ y) X0 X1 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ y)) = (M.op X0 (M.op (σ x) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y) X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : (M.op y (σ y)) = (M.op y (σ x)) := by
          first
          | (have i₁ := b3e48
             have i₂ := b3e36 (σ x) (σ x)
             grind)
          | exact superpose b3e36 b3e48
          | exact resolve b3e48 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e67 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e71 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e67
        have b3e72 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e71
          | exact resolve b3e71 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e70 (σ X0)
             grind)
          | exact superpose b3e70 b3e18
          | exact resolve b3e18 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e80 X0
             have i₂ := b3e70 X0
             grind)
          | exact superpose b3e70 b3e80
          | exact resolve b3e80 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70 b3e80
        have b3e89 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e91 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e89
        have b3e92 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e91
             have r₂ := b3e23
             grind)
          | exact resolve b3e91 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e91
        have b3e128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e177 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ (k x y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ x) X0 X1 (σ x)
             have i₂ := b3e72
             grind)
          | exact superpose b3e72 b3e12
          | exact resolve b3e12 b3e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e178 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ (k x y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ x) (σ x) X1
             have i₂ := b3e72
             grind)
          | exact superpose b3e72 b3e12
          | exact resolve b3e12 b3e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ (M.op x x))) := by
          intro X0 X1
          first
          | (have i₁ := b3e178 X0 X1
             have i₂ := b3e92
             grind)
          | exact superpose b3e92 b3e178
          | exact resolve b3e178 b3e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e178
        have b3e181 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ (M.op x x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e177 X0 X1
             have i₂ := b3e92
             grind)
          | exact superpose b3e92 b3e177
          | exact resolve b3e177 b3e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e177
        have b3e218 : ∀ X0 X1 : G, (M.op (σ (k x y)) X1) = (M.op (M.op X0 (σ x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e34 X0 (σ x) X1 (σ x)
             have i₂ := b3e72
             grind)
          | exact superpose b3e72 b3e34
          | exact resolve b3e34 b3e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e264 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (M.op X0 (σ x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e218 X0 X1
             have i₂ := b3e92
             grind)
          | exact superpose b3e92 b3e218
          | exact resolve b3e218 b3e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e218
        have b3e306 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ x))) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e39 X0 X1 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e39
          | exact resolve b3e39 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e308 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e39 X0 X1 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e39
          | exact resolve b3e39 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e309 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e39 X1 X2 (M.op X3 X0) y
             have i₂ := b3e36 X3 X0
             grind)
          | exact superpose b3e36 b3e39
          | exact resolve b3e39 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e378 : ∀ X0 X1 : G, (M.op X0 (σ (k x y))) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e306 X0 X1
             have i₂ := b3e72
             grind)
          | exact superpose b3e72 b3e306
          | exact resolve b3e306 b3e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72 b3e306
        have b3e389 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x x))) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e378 X0 X1
             have i₂ := b3e92
             grind)
          | exact superpose b3e92 b3e378
          | exact resolve b3e378 b3e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92 b3e378
        have b3e407 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X2 X0) y) := by
          intro X0 X2
          first
          | (have i₁ := b3e12 X0 x y X2
             have i₂ := b3e308 X0 x
             grind)
          | exact superpose b3e308 b3e12
          | exact resolve b3e12 b3e308
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e308
        have b3e1020 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ x) (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (σ x) X2 X1 (σ x)
             have i₂ := b3e49 X0 X1
             grind)
          | exact superpose b3e49 b3e12
          | exact resolve b3e12 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1428 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ X0)) = (M.op (σ y) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b3e49 (σ X0) (σ X0)
             have i₂ := b3e83 X0
             grind)
          | exact superpose b3e83 b3e49
          | exact resolve b3e49 b3e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e1433 : ∀ X0 : G, (M.op (σ y) (σ (M.op X0 X0))) = (M.op (σ (M.op x x)) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e1428 X0
             have i₂ := b3e264 (σ x) (σ X0)
             grind)
          | exact superpose b3e264 b3e1428
          | exact resolve b3e1428 b3e264
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e264 b3e1428
        have b3e3043 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b3e128 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e3044 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b3e3043 X0
             have j1 := b3e15 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b3e3043 X0
             have r₂ := b3e15 X0 (M.op X0 X0)
             grind)
          | exact resolve b3e3043 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3043
        have b3e3538 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b3e3044 (σ X0)
             have i₂ := b3e83 X0
             grind)
          | exact superpose b3e83 b3e3044
          | exact resolve b3e3044 b3e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3547 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b3e3538 X0
             have i₂ := b3e18 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e18 b3e3538
          | exact resolve b3e3538 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3538
        have b3e3573 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b3e3547 X0
             have i₂ := b3e3044 X0
             grind)
          | exact superpose b3e3044 b3e3547
          | exact resolve b3e3547 b3e3044
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3044 b3e3547
        have b3e10842 : (M.op (M.op y (σ x)) (σ x)) = (M.op (σ y) (σ (M.op x x))) := by
          first
          | (have i₁ := b3e180 (σ y) y
             have i₂ := b3e51
             grind)
          | exact superpose b3e51 b3e180
          | exact resolve b3e180 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e10982 : (M.op (σ y) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
          first
          | (have i₁ := b3e10842
             have i₂ := b3e180 (σ x) y
             grind)
          | exact superpose b3e180 b3e10842
          | exact resolve b3e10842 b3e180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e180 b3e10842
        have b3e11025 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op x (M.op x x))) := by
          first
          | (have i₁ := b3e10982
             have i₂ := b3e3573 x
             grind)
          | exact superpose b3e3573 b3e10982
          | exact resolve b3e10982 b3e3573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10982
        have b3e11524 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e181 (M.op x X0) (σ y)
             have i₂ := b3e50 X0 x
             grind)
          | exact superpose b3e50 b3e181
          | exact resolve b3e181 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e181
        have b3e11866 : (M.op (σ (M.op x x)) (σ y)) = (M.op (σ x) (M.op y (σ x))) := by
          first
          | (have i₁ := b3e11524 x
             have i₂ := b3e309 (σ x) (σ x) x (σ x)
             grind)
          | exact superpose b3e309 b3e11524
          | exact resolve b3e11524 b3e309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11524
        have b3e11937 : (M.op (σ x) (M.op y (σ x))) = (M.op (σ y) (σ (M.op y y))) := by
          first
          | (have i₁ := b3e11866
             have i₂ := b3e1433 y
             grind)
          | exact superpose b3e1433 b3e11866
          | exact resolve b3e11866 b3e1433
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1433 b3e11866
        have b3e11966 : (M.op (σ x) (M.op y (σ x))) = (σ (M.op y (M.op y y))) := by
          first
          | (have i₁ := b3e11937
             have i₂ := b3e3573 y
             grind)
          | exact superpose b3e3573 b3e11937
          | exact resolve b3e11937 b3e3573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11937
        have b3e11979 : (σ (M.op y y)) = (M.op (σ x) (M.op y (σ x))) := by
          first
          | (have i₁ := b3e11966
             have i₂ := b3e36 y y
             grind)
          | exact superpose b3e36 b3e11966
          | exact resolve b3e11966 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11966
        have b3e12438 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e39 (σ x) X0 (σ x) y
             have i₂ := b3e11979
             grind)
          | exact superpose b3e11979 b3e39
          | exact resolve b3e39 b3e11979
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e11979
        have b3e13518 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op x x))) := by
          first
          | (have i₁ := b3e12438 (σ x)
             have i₂ := b3e83 x
             grind)
          | exact superpose b3e83 b3e12438
          | exact resolve b3e12438 b3e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12438
        have b3e13660 : (σ (M.op y y)) = (σ (M.op x (M.op x x))) := by
          first
          | (have i₁ := b3e13518
             have i₂ := b3e3573 x
             grind)
          | exact superpose b3e3573 b3e13518
          | exact resolve b3e13518 b3e3573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3573 b3e13518
        have b3e14241 : (M.op x (M.op x x)) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b3e13 (M.op x (M.op x x))
             have i₂ := b3e13660
             grind)
          | exact superpose b3e13660 b3e13
          | exact resolve b3e13 b3e13660
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e14260 : (M.op y y) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b3e14241
             have i₂ := b3e13 (M.op y y)
             grind)
          | exact superpose b3e13 b3e14241
          | exact resolve b3e14241 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14241
        have b3e14893 : (M.op y (M.op y y)) = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b3e36 x (M.op x x)
             have i₂ := b3e14260
             grind)
          | exact superpose b3e14260 b3e36
          | exact resolve b3e36 b3e14260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e14926 : (M.op (M.op y y) y) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b3e407 (M.op x x) x
             have i₂ := b3e14260
             grind)
          | exact superpose b3e14260 b3e407
          | exact resolve b3e407 b3e14260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14260
        have b3e14927 : (M.op x y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b3e14926
             have i₂ := b3e407 x x
             grind)
          | exact superpose b3e407 b3e14926
          | exact resolve b3e14926 b3e407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14926
        have b3e14951 : (M.op y x) = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b3e14893
             have i₂ := b3e36 x x
             grind)
          | exact superpose b3e36 b3e14893
          | exact resolve b3e14893 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14893
        have b3e14966 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b3e14927
             have i₂ := b3e407 y y
             grind)
          | exact superpose b3e407 b3e14927
          | exact resolve b3e14927 b3e407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e407 b3e14927
        have b3e14989 : (M.op y y) = (M.op y x) := by
          first
          | (have i₁ := b3e14951
             have i₂ := b3e36 y y
             grind)
          | exact superpose b3e36 b3e14951
          | exact resolve b3e14951 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e14951
        have b3e14999 : y = (M.op y y) := by
          first
          | (have i₁ := b3e14966
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e14966
          | exact resolve b3e14966 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14966
        have b3e17121 : y = (M.op y x) := by
          first
          | (have i₁ := b3e14999
             have i₂ := b3e14989
             grind)
          | exact superpose b3e14989 b3e14999
          | exact resolve b3e14999 b3e14989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14999
        have b3e25605 : ∀ X0 : G, (M.op (σ y) (σ (M.op x x))) = (M.op (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e389 (σ y) x
             have i₂ := b3e1020 x (σ y) X0
             grind)
          | exact superpose b3e1020 b3e389
          | exact resolve b3e389 b3e1020
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e389
        have b3e25873 : ∀ X0 : G, (σ (M.op x (M.op x x))) = (M.op (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e25605 X0
             have i₂ := b3e11025
             grind)
          | exact superpose b3e11025 b3e25605
          | exact resolve b3e25605 b3e11025
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11025 b3e25605
        have b3e26099 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e25873 X0
             have i₂ := b3e13660
             grind)
          | exact superpose b3e13660 b3e25873
          | exact resolve b3e25873 b3e13660
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13660 b3e25873
        have b3e26200 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (σ (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b3e26099 X0
             have i₂ := b3e14989
             grind)
          | exact superpose b3e14989 b3e26099
          | exact resolve b3e26099 b3e14989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26099
        have b3e26244 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e26200 X0
             have i₂ := b3e17121
             grind)
          | exact superpose b3e17121 b3e26200
          | exact resolve b3e26200 b3e17121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26200
        have b3e37496 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e38 (σ x) x (σ y) X0 X1
             have i₂ := b3e26244 x
             grind)
          | exact superpose b3e26244 b3e38
          | exact resolve b3e38 b3e26244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e37577 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op X1 (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1020 X0 (M.op X1 (σ y)) (σ x)
             have i₂ := b3e26244 X1
             grind)
          | exact superpose b3e26244 b3e1020
          | exact resolve b3e1020 b3e26244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1020 b3e26244
        have b3e37592 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (σ y))) := by
          first
          | (have i₁ := b3e37577 x x
             have i₂ := b3e309 (σ y) (σ y) x x
             grind)
          | exact superpose b3e309 b3e37577
          | exact resolve b3e37577 b3e309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e309 b3e37577
        have b3e37663 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e37592
             have i₂ := b3e37496 y (σ y)
             grind)
          | exact superpose b3e37496 b3e37592
          | exact resolve b3e37592 b3e37496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37496 b3e37592
        have b3e37717 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e37663
             have i₂ := b3e83 y
             grind)
          | exact superpose b3e83 b3e37663
          | exact resolve b3e37663 b3e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83 b3e37663
        have b3e37761 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e37717
             have i₂ := b3e14989
             grind)
          | exact superpose b3e14989 b3e37717
          | exact resolve b3e37717 b3e14989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14989 b3e37717
        have b3e37786 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e37761
             have i₂ := b3e17121
             grind)
          | exact superpose b3e17121 b3e37761
          | exact resolve b3e37761 b3e17121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17121 b3e37761
        have b3e41570 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e37786
             grind)
          | exact superpose b3e37786 b3e22
          | exact resolve b3e22 b3e37786
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37786
        have b3e41667 : False := by grind
        exact b3e41667
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (σ y) ≠ (σ y) := by
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
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b5e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e74 X0
               have i₂ := b5e66 X0
               grind)
            | exact superpose b5e66 b5e74
            | exact resolve b5e74 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e74
          have b5e83 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b5e85 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b5e83
          have b5e86 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e85
               have r₂ := b5e25
               grind)
            | exact resolve b5e85 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e85
          have b5e102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e102 X0 X1
               have i₂ := b5e77 X0
               grind)
            | exact superpose b5e77 b5e102
            | (have j0 := b5e102 X0 X1
               grind)
            | exact resolve b5e102 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e8411 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e134 x y
               grind)
            | exact superpose b5e134 b5e23
            | (have j1 := b5e134 x y
               grind)
            | exact resolve b5e23 b5e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e134
          have b5e8533 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e8411
               have r₂ := b5e24
               grind)
            | exact resolve b5e8411 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8411
          have b5e8547 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e8533
               have i₂ := b5e86
               grind)
            | exact superpose b5e86 b5e8533
            | exact resolve b5e8533 b5e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86 b5e8533
          have b5e8553 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e8547
               have r₂ := b5e77 x
               grind)
            | exact resolve b5e8547 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8547
          have b5e8557 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e8553
               grind)
            | exact superpose b5e8553 b5e23
            | exact resolve b5e23 b5e8553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8553
          have b5e8618 : False := by grind
          exact b5e8618
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e62 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e60
        have b6e63 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e62
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e62
          | exact resolve b6e62 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e80 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e63
             grind)
          | exact superpose b6e63 b6e23
          | exact resolve b6e23 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e63
        have b6e127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e80
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e80
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e80 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e128 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
        clear b6e127
        have b6e129 : y = (M.op x y) := by
          first
          | (have r₁ := b6e128
             have r₂ := b6e20
             grind)
          | exact resolve b6e128 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128
        have b6e130 : False := by grind
        exact b6e130
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e56 (σ X0)
               grind)
            | exact superpose b7e56 b7e19
            | exact resolve b7e19 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e58 X0
               have i₂ := b7e56 X0
               grind)
            | exact superpose b7e56 b7e58
            | exact resolve b7e58 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56 b7e58
          have b7e67 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e70 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e67
          have b7e71 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e25
               grind)
            | exact resolve b7e70 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e70
          have b7e72 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
          have b7e73 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e63 x
               grind)
            | exact superpose b7e63 b7e72
            | exact resolve b7e72 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e72
          have b7e76 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e14
            | exact resolve b7e14 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e77 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e76
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e76
            | exact resolve b7e76 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e118 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e119 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b7e118
          have b7e121 : y = (M.op x y) := by
            first
            | (have r₁ := b7e119
               have r₂ := b7e21
               grind)
            | exact resolve b7e119 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119
          have b7e123 : False := by grind
          exact b7e123
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e51 (σ X0)
               grind)
            | exact superpose b8e51 b8e19
            | exact resolve b8e19 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e53 X0
               have i₂ := b8e51 X0
               grind)
            | exact superpose b8e51 b8e53
            | exact resolve b8e53 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51 b8e53
          have b8e78 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e18 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e18 X1 X1
               have i₂ := b8e18 X1 X1
               grind)
            | exact superpose b8e18 b8e18
            | (have j0 := b8e18 X0 X2
               have j1 := b8e18 X0 X2
               grind)
            | exact resolve b8e18 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e90 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X1 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X2
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 (M.op X0 X0)
               have r₂ := b8e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e82 X0 X1
               have i₂ := b8e58 X0
               grind)
            | exact superpose b8e58 b8e82
            | (have j0 := b8e82 X0 X1
               grind)
            | exact resolve b8e82 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e107 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e78 X0 X2 X2
               have j1 := b8e90 X0 X2 X2
               grind)
            | (have r₁ := b8e78 X0 X1 X2
               have r₂ := b8e90 X0 X1 X2
               grind)
            | (have r₁ := b8e78 X0 X2 X1
               have r₂ := b8e90 X0 X1 X2
               grind)
            | (have r₁ := b8e78 X0 X1 (M.op X0 X2)
               have r₂ := b8e90 X0 (M.op X0 X2) X2
               grind)
            | exact resolve b8e78 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78 b8e90
          have b8e7721 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e107 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e7722 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e7721 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7721
          have b8e7723 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e7722 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7722
          have b8e8639 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e103 x y
               grind)
            | exact superpose b8e103 b8e20
            | (have j1 := b8e103 x y
               grind)
            | exact resolve b8e20 b8e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e8819 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e8639
               have r₂ := b8e24
               grind)
            | exact resolve b8e8639 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8639
          have b8e124281 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e8819
               have i₂ := b8e7723 x y
               grind)
            | exact superpose b8e7723 b8e8819
            | (have j1 := b8e7723 x y
               grind)
            | exact resolve b8e8819 b8e7723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7723 b8e8819
          have b8e124282 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x y) := by grind
          clear b8e124281
          have b8e124287 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e124282
               have r₂ := b8e22
               grind)
            | exact resolve b8e124282 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124282
          have b8e124291 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e124287
               grind)
            | exact superpose b8e124287 b8e23
            | exact resolve b8e23 b8e124287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124287
          have b8e124696 : False := by grind
          exact b8e124696
