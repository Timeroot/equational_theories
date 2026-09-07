import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3317`: `x ◇ y = x ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_x_pxy_Equation3317 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3317 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3317.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e37 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) := by
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
        have b1e40 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (M.op X0 x)
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b1e37 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e37
          | exact resolve b1e37 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e56 : y = (M.op x x) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e50
          | exact resolve b1e50 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e70 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e40 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e40
          | exact resolve b1e40 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e206 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (σ X0) (σ X1)
             have i₂ := b1e60 X0 X1
             grind)
          | exact superpose b1e60 b1e16
          | (have j0 := b1e16 (σ X0) (σ X1)
             have j1 := b1e60 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X0) (σ X1)
             have r₂ := b1e60 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X1) (σ X0)
             have r₂ := b1e60 X0 X1
             grind)
          | exact resolve b1e16 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e213 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e206 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e206
        have b1e214 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e213 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e213
        have b1e222 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e214 X0 X1
             have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b1e214 X0 X1
             have r₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e214 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e214
        have b1e233 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e222 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e222
          | (have j0 := b1e222 X0 X1
             grind)
          | exact resolve b1e222 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e222
        have b1e812 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e70
             have i₂ := b1e233 x x
             grind)
          | exact superpose b1e233 b1e70
          | (have j1 := b1e233 x x
             grind)
          | exact resolve b1e70 b1e233
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e233
        have b1e4700 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e812
             grind)
          | exact superpose b1e812 b1e21
          | exact resolve b1e21 b1e812
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e812
        have b1e5263 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e4700
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e4700
          | (have j1 := b1e17 x x
             grind)
          | exact resolve b1e4700 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4700
        have b1e5264 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e5263
        have b1e5265 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e5264
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e5264
          | exact resolve b1e5264 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5264
        have b1e5266 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e5265
        have b1e5269 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e5266
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e5266
          | exact resolve b1e5266 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5266
        have b1e5271 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e5269
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e5269
          | exact resolve b1e5269 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e5269
        have b1e5427 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e5271
             grind)
          | exact superpose b1e5271 b1e13
          | exact resolve b1e13 b1e5271
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5271
        have b1e5495 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e5427
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e5427
          | exact resolve b1e5427 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5427
        have b1e5496 : x = y := by grind
        clear b1e5495
        have b1e5557 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e5496
             grind)
          | exact superpose b1e5496 b1e21
          | exact resolve b1e21 b1e5496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5558 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e5496
             grind)
          | exact superpose b1e5496 b1e22
          | exact resolve b1e22 b1e5496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5496
        have b1e5604 : False := by grind
        exact b1e5604
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e30 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e18 (k (τ X0) X1) X2
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e18
          | exact resolve b2e18 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) := by
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
        have b2e34 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op X0 x)
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b2e32 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e32
          | exact resolve b2e32 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e40 : y = (M.op x x) := by
          first
          | (have i₁ := b2e36
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e36
          | exact resolve b2e36 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e41 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
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
        have b2e44 : x = (M.op y x) ∨ y = (k y x) := by grind
        clear b2e41
        have b2e47 : y = (k y x) := by
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
        have b2e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e52 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e26 X0 X1
             have i₂ := b2e17 (τ X0) X1
             grind)
          | exact superpose b2e17 b2e26
          | (have j1 := b2e17 (τ X0) X1
             grind)
          | exact resolve b2e26 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e34 X0 (M.op X1 (M.op X0 X2))
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e34
          | exact resolve b2e34 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (M.op X1 X0) X0
             have i₂ := b2e34 X1 X0
             grind)
          | exact superpose b2e34 b2e16
          | (have j0 := b2e16 (M.op X1 X0) X0
             grind)
          | (have r₁ := b2e16 (M.op X1 X1) X1
             have r₂ := b2e34 X1 X1
             grind)
          | exact resolve b2e16 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 (M.op X1 X0)
             have i₂ := b2e34 X1 X0
             grind)
          | exact superpose b2e34 b2e15
          | (have j0 := b2e15 X0 (M.op X1 X0)
             grind)
          | (have r₁ := b2e15 X1 (M.op X1 X1)
             have r₂ := b2e34 X1 X1
             grind)
          | exact resolve b2e15 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have j0 := b2e64 X0 X1
             have j1 := b2e15 (M.op X1 X0) X0
             grind)
          | (have r₁ := b2e64 X1 X1
             have r₂ := b2e15 (M.op X1 X1) X1
             grind)
          | exact resolve b2e64 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e78 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e27 X1 X0
             grind)
          | exact superpose b2e27 b2e13
          | exact resolve b2e13 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e90 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e31
          | exact resolve b2e31 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e109 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e78 (k (τ X0) X1) X2
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e78
          | exact resolve b2e78 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e139 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ X0) (M.op X2 (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (σ X0) X2 (σ X1)
             have i₂ := b2e51 X0 X1
             grind)
          | exact superpose b2e51 b2e12
          | (have j1 := b2e51 X0 X1
             grind)
          | exact resolve b2e12 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e141 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e51 y x
             grind)
          | exact superpose b2e51 b2e21
          | (have j1 := b2e51 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e51 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e51 x y
             grind)
          | exact resolve b2e21 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e145 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X0) (σ X1)
             have i₂ := b2e51 X0 X1
             grind)
          | exact superpose b2e51 b2e16
          | (have j0 := b2e16 (σ X0) (σ X1)
             have j1 := b2e51 X0 X1
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
        have b2e148 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e51 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e150 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e148 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e148
        have b2e152 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e145 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e145
        have b2e153 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e152 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e152
        have b2e154 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e141
        have b2e158 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e153 X0 X1
             have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b2e153 X0 X1
             have r₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e153 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e153
        have b2e159 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e154
             have r₂ := b2e22
             grind)
          | exact resolve b2e154 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e154
        have b2e164 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e158 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e158
          | (have j0 := b2e158 X0 X1
             grind)
          | exact resolve b2e158 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e158
        have b2e165 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e159
             have i₂ := b2e47
             grind)
          | exact superpose b2e47 b2e159
          | exact resolve b2e159 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159
        have b2e166 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e165
             grind)
          | exact superpose b2e165 b2e22
          | exact resolve b2e22 b2e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e165
        have b2e274 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e66 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e467 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e150 (τ X0)
             have i₂ := b2e27 X0 (τ X0)
             grind)
          | exact superpose b2e27 b2e150
          | (have j0 := b2e150 (τ X0)
             grind)
          | exact resolve b2e150 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150
        have b2e469 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e467 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e467
          | (have j0 := b2e467 X0
             grind)
          | exact resolve b2e467 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e467
        have b2e472 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e469 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e469
          | (have j0 := b2e469 X0
             grind)
          | exact resolve b2e469 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e469
        have b2e542 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e67 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e564 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b2e31 (M.op (σ X0) (σ X0)) X0
             have i₂ := b2e542 (σ X0)
             grind)
          | exact superpose b2e542 b2e31
          | exact resolve b2e31 b2e542
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e599 : ∀ X0 : G, (M.op (M.op x (M.op x X0)) x) = (M.op (M.op x (M.op x X0)) y) := by
          intro X0
          first
          | (have i₁ := b2e61 x x X0
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e61
          | exact resolve b2e61 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e643 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e164 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e164
          | exact resolve b2e164 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e688 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e643 X0 X1
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e643
          | (have j0 := b2e643 X0 X1
             grind)
          | exact resolve b2e643 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e643
        have b2e692 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e688 X0 X1
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e688
          | (have j0 := b2e688 X0 X1
             grind)
          | exact resolve b2e688 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e688
        have b2e718 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e78 (M.op (τ X0) X1) X2
             have i₂ := b2e52 X0 X1
             grind)
          | exact superpose b2e52 b2e78
          | (have j1 := b2e52 X0 X1
             grind)
          | exact resolve b2e78 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e725 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e718 X0 X1 X2
             have i₂ := b2e109 X0 X1 X2
             grind)
          | exact superpose b2e109 b2e718
          | (have j0 := b2e718 X0 X1 X2
             grind)
          | exact resolve b2e718 b2e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109 b2e718
        have b2e1128 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ X0)) (M.op X2 (σ (τ (k X0 X1))))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e139 (τ X0) (τ X1) X2
             have i₂ := b2e90 X1 X0
             grind)
          | exact superpose b2e90 b2e139
          | (have j0 := b2e139 (τ X0) (τ X1) X2
             grind)
          | exact resolve b2e139 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e139
        have b2e1160 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ X0)) (M.op X2 (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1128 X0 X1 X2
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e1128
          | (have j0 := b2e1128 X0 X1 X2
             grind)
          | exact resolve b2e1128 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1128
        have b2e1164 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1160 X0 X1 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1160
          | (have j0 := b2e1160 X0 X1 X2
             grind)
          | exact resolve b2e1160 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1160
        have b2e1166 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1164 X0 X1 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1164
          | (have j0 := b2e1164 X0 X1 X2
             grind)
          | exact resolve b2e1164 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1164
        have b2e1167 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1166 X0 X1 X2
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e1166
          | (have j0 := b2e1166 X0 X1 X2
             grind)
          | exact resolve b2e1166 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1166
        have b2e1168 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1167 X0 X0 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1167
          | (have j0 := b2e1167 X0 X1 X2
             grind)
          | exact resolve b2e1167 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1167
        have b2e1169 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1168 X0 X1 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1168
          | (have j0 := b2e1168 X0 X1 X2
             grind)
          | exact resolve b2e1168 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1168
        have b2e2834 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e692 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e692
          | exact resolve b2e692 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2849 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X0 X1
             have i₂ := b2e692 X0 X1
             grind)
          | exact superpose b2e692 b2e31
          | (have j1 := b2e692 X0 X1
             grind)
          | exact resolve b2e31 b2e692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e692
        have b2e6628 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e564 x
             have i₂ := b2e164 x x
             grind)
          | exact superpose b2e164 b2e564
          | (have j1 := b2e164 X0 X0
             grind)
          | exact resolve b2e564 b2e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e164
        have b2e6629 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e564 x
             have i₂ := b2e51 x x
             grind)
          | exact superpose b2e51 b2e564
          | (have j1 := b2e51 X0 X0
             grind)
          | exact resolve b2e564 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e6677 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e6629 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6629
        have b2e6712 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e6677 X0
             have i₂ := b2e13 (k X0 X0)
             grind)
          | exact superpose b2e13 b2e6677
          | (have j0 := b2e6677 X0
             grind)
          | exact resolve b2e6677 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6677
        have b2e6713 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e6628 X0
             have i₂ := b2e13 (k X0 X0)
             grind)
          | exact superpose b2e13 b2e6628
          | (have j0 := b2e6628 X0
             grind)
          | exact resolve b2e6628 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6628
        have b2e9949 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e2849 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e2849
          | exact resolve b2e2849 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2849
        have b2e10042 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e9949 X0 X1
             have i₂ := b2e90 X0 X1
             grind)
          | exact superpose b2e90 b2e9949
          | (have j0 := b2e9949 X0 X1
             grind)
          | exact resolve b2e9949 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9949
        have b2e10176 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e90 X2 (k X0 X1)
             have i₂ := b2e10042 X1 X0
             grind)
          | exact superpose b2e10042 b2e90
          | (have j1 := b2e10042 X1 X0
             grind)
          | exact resolve b2e90 b2e10042
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10042
        have b2e10232 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e10176 X0 X1 X2
             have i₂ := b2e90 X2 (M.op X0 X1)
             grind)
          | exact superpose b2e90 b2e10176
          | (have j0 := b2e10176 X0 X1 X2
             grind)
          | exact resolve b2e10176 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10176
        have b2e11454 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e27 X0 (k (τ X0) (τ X0))
             have i₂ := b2e6713 (τ X0)
             grind)
          | exact superpose b2e6713 b2e27
          | (have j1 := b2e6713 (τ X0)
             grind)
          | exact resolve b2e27 b2e6713
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6713
        have b2e11492 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e11454 X0
             have i₂ := b2e27 X0 (τ X0)
             grind)
          | exact superpose b2e27 b2e11454
          | (have j0 := b2e11454 X0
             grind)
          | exact resolve b2e11454 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11454
        have b2e11531 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e11492 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e11492
          | (have j0 := b2e11492 X0
             grind)
          | exact resolve b2e11492 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11492
        have b2e11566 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b2e11531 X0
             have i₂ := b2e27 X0 (τ X0)
             grind)
          | exact superpose b2e27 b2e11531
          | (have j0 := b2e11531 X0
             grind)
          | exact resolve b2e11531 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e11531
        have b2e11601 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e11566 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e11566
          | (have j0 := b2e11566 X0
             grind)
          | exact resolve b2e11566 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11566
        have b2e22394 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e725 X0 (τ X0) X0
             have i₂ := b2e11601 (τ X0)
             grind)
          | exact superpose b2e11601 b2e725
          | (have j0 := b2e725 X0 (τ X0) x
             have j1 := b2e11601 (τ X0)
             grind)
          | exact resolve b2e725 b2e11601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e725 b2e11601
        have b2e22463 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
          intro X0
          first
          | (have j0 := b2e22394 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22394
        have b2e22506 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have j0 := b2e22463 X0
             have j1 := b2e472 (τ X0)
             grind)
          | (have r₁ := b2e22463 X0
             have r₂ := b2e472 (τ X0)
             grind)
          | exact resolve b2e22463 b2e472
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22463
        have b2e22556 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e22506 X0
             have i₂ := b2e542 (τ X0)
             grind)
          | exact superpose b2e542 b2e22506
          | (have j0 := b2e22506 X0
             grind)
          | exact resolve b2e22506 b2e542
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22506
        have b2e22589 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e22556 X0
             have i₂ := b2e90 X0 X0
             grind)
          | exact superpose b2e90 b2e22556
          | (have j0 := b2e22556 X0
             grind)
          | exact resolve b2e22556 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22556
        have b2e27633 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e6712 (τ X0)
             have i₂ := b2e90 X0 X0
             grind)
          | exact superpose b2e90 b2e6712
          | (have j0 := b2e6712 (τ X0)
             grind)
          | exact resolve b2e6712 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6712
        have b2e27765 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e27633 X0
             have i₂ := b2e90 X0 (k X0 X0)
             grind)
          | exact superpose b2e90 b2e27633
          | (have j0 := b2e27633 X0
             grind)
          | exact resolve b2e27633 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27633
        have b2e27817 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27765 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e27765
          | (have j0 := b2e27765 X0
             grind)
          | exact resolve b2e27765 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27765
        have b2e50787 : ∀ X0 X1 X2 : G, (τ (σ (k (k (τ X0) X1) X2))) = (τ (k (M.op X0 (σ X1)) (σ X2))) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e10232 X0 (σ X1) (σ X2)
             have i₂ := b2e30 X0 X1 X2
             grind)
          | exact superpose b2e30 b2e10232
          | (have j0 := b2e10232 X0 (σ X1) X2
             grind)
          | exact resolve b2e10232 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e50835 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27817 X0
             have i₂ := b2e10232 X0 X0 X0
             grind)
          | exact superpose b2e10232 b2e27817
          | (have j0 := b2e27817 X0
             have j1 := b2e10232 X0 X0 x
             grind)
          | exact resolve b2e27817 b2e10232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10232 b2e27817
        have b2e50987 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e50835 X0
             have j1 := b2e472 X0
             grind)
          | (have r₁ := b2e50835 X0
             have r₂ := b2e472 X0
             grind)
          | exact resolve b2e50835 b2e472
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e472 b2e50835
        have b2e51001 : ∀ X0 X1 X2 : G, (τ (σ (k (k (τ X0) X1) X2))) = (k (τ (M.op X0 (σ X1))) X2) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e50787 X0 X1 X2
             have i₂ := b2e31 (M.op X0 (σ X1)) X2
             grind)
          | exact superpose b2e31 b2e50787
          | (have j0 := b2e50787 X0 X1 X2
             grind)
          | exact resolve b2e50787 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e50787
        have b2e51022 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e50987 X0
             have i₂ := b2e542 X0
             grind)
          | exact superpose b2e542 b2e50987
          | (have j0 := b2e50987 X0
             grind)
          | exact resolve b2e50987 b2e542
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e542 b2e50987
        have b2e51026 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) X2) = (k (τ (M.op X0 (σ X1))) X2) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e51001 X0 X1 X2
             have i₂ := b2e13 (k (k (τ X0) X1) X2)
             grind)
          | exact superpose b2e13 b2e51001
          | (have j0 := b2e51001 X0 X1 X2
             grind)
          | exact resolve b2e51001 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51001
        have b2e51418 : ∀ X0 X1 : G, (τ (k (k X0 X0) X1)) = (k (τ (M.op X0 X0)) (τ X1)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e90 X1 (k X0 X0)
             have i₂ := b2e51022 X0
             grind)
          | exact superpose b2e51022 b2e90
          | (have j1 := b2e51022 X0
             grind)
          | exact resolve b2e90 b2e51022
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51022
        have b2e51536 : ∀ X0 X1 : G, (τ (k (k X0 X0) X1)) = (τ (k (M.op X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e51418 X0 X1
             have i₂ := b2e90 X1 (M.op X0 X0)
             grind)
          | exact superpose b2e90 b2e51418
          | (have j0 := b2e51418 X0 X1
             grind)
          | exact resolve b2e51418 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90 b2e51418
        have b2e78541 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e34 (τ X0) (τ X0)
             have i₂ := b2e22589 X0
             grind)
          | exact superpose b2e22589 b2e34
          | (have j1 := b2e22589 X0
             grind)
          | exact resolve b2e34 b2e22589
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22589
        have b2e91179 : ∀ X0 X1 : G, (k (k X0 X0) X1) = (σ (τ (k (M.op X0 X0) X1))) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e14 (k (k X0 X0) X1)
             have i₂ := b2e51536 X0 X1
             grind)
          | exact superpose b2e51536 b2e14
          | (have j1 := b2e51536 X0 X1
             grind)
          | exact resolve b2e14 b2e51536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51536
        have b2e91252 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (k (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e91179 X0 X1
             have i₂ := b2e14 (k (M.op X0 X0) X1)
             grind)
          | exact superpose b2e14 b2e91179
          | (have j0 := b2e91179 X0 X1
             grind)
          | exact resolve b2e91179 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91179
        have b2e203682 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e564 X0
             have i₂ := b2e51026 (σ X0) X0 X0
             grind)
          | exact superpose b2e51026 b2e564
          | (have j1 := b2e51026 (σ X0) X0 x
             grind)
          | exact resolve b2e564 b2e51026
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e564 b2e51026
        have b2e203716 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (k X0 X0) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e203682 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e203682
          | (have j0 := b2e203682 X0
             grind)
          | exact resolve b2e203682 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e203682
        have b2e203725 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e203716 X0
             have i₂ := b2e18 X0 X0
             grind)
          | exact superpose b2e18 b2e203716
          | (have j0 := b2e203716 X0
             grind)
          | exact resolve b2e203716 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e203716
        have b2e204040 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e14 (M.op (σ X0) (σ X0))
             have i₂ := b2e203725 X0
             grind)
          | exact superpose b2e203725 b2e14
          | (have j1 := b2e203725 X0
             grind)
          | exact resolve b2e14 b2e203725
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e203725
        have b2e248393 : ∀ X0 : G, (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e78541 (σ X0)
             have i₂ := b2e78 X0 (σ X0)
             grind)
          | exact superpose b2e78 b2e78541
          | (have j0 := b2e78541 (σ X0)
             grind)
          | exact resolve b2e78541 b2e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e78 b2e78541
        have b2e248408 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e248393 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e248393
          | (have j0 := b2e248393 X0
             grind)
          | exact resolve b2e248393 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e248393
        have b2e248412 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e248408 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e248408
          | (have j0 := b2e248408 X0
             grind)
          | exact resolve b2e248408 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e248408
        have b2e248480 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e34 X0 (k X0 X0)
             have i₂ := b2e248412 X0
             grind)
          | exact superpose b2e248412 b2e34
          | (have j1 := b2e248412 X0
             grind)
          | exact resolve b2e34 b2e248412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e248543 : (M.op (M.op x (k x x)) x) = (M.op (M.op x (k x x)) y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e599 (k x x)
             have i₂ := b2e248412 x
             grind)
          | exact superpose b2e248412 b2e599
          | (have j1 := b2e248412 x
             grind)
          | exact resolve b2e599 b2e248412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e599
        have b2e248613 : (M.op (M.op x (k x x)) x) = (M.op (M.op x (k x x)) y) ∨ x = y := by
          first
          | (have i₁ := b2e248543
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e248543
          | exact resolve b2e248543 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e248543
        have b2e249108 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e274 (k X0 X0)
             have i₂ := b2e248480 X0
             grind)
          | exact superpose b2e248480 b2e274
          | (have j1 := b2e248480 X0
             grind)
          | exact resolve b2e274 b2e248480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e274 b2e248480
        have b2e249279 : (M.op (k x x) y) = (M.op (k x x) x) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e248613
             have i₂ := b2e248412 x
             grind)
          | exact superpose b2e248412 b2e248613
          | (have j1 := b2e248412 x
             grind)
          | exact resolve b2e248613 b2e248412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e248613
        have b2e249286 : x = y ∨ (M.op (k x x) y) = (M.op (k x x) x) ∨ x = y := by
          first
          | (have i₁ := b2e249279
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e249279
          | exact resolve b2e249279 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e249279
        have b2e249287 : (M.op (k x x) y) = (M.op (k x x) x) ∨ x = y := by grind
        clear b2e249286
        have b2e249540 : (k x x) = (k (k x x) (M.op (k x x) y)) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e249108 x
             have i₂ := b2e249287
             grind)
          | exact superpose b2e249287 b2e249108
          | (have j0 := b2e249108 x
             grind)
          | exact resolve b2e249108 b2e249287
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e249108 b2e249287
        have b2e249562 : x = y ∨ (k x x) = (k (k x x) (M.op (k x x) y)) ∨ x = y := by
          first
          | (have i₁ := b2e249540
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e249540
          | exact resolve b2e249540 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e249540
        have b2e249563 : (k x x) = (k (k x x) (M.op (k x x) y)) ∨ x = y := by grind
        clear b2e249562
        have b2e249599 : (k x x) = (k (M.op x x) (M.op (k x x) y)) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e91252 x (M.op (k x x) y)
             have i₂ := b2e249563
             grind)
          | exact superpose b2e249563 b2e91252
          | (have j0 := b2e91252 x x
             grind)
          | exact resolve b2e91252 b2e249563
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91252 b2e249563
        have b2e249610 : (k x x) = (k y (M.op (k x x) y)) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e249599
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e249599
          | exact resolve b2e249599 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e249599
        have b2e249623 : x = y ∨ (k x x) = (k y (M.op (k x x) y)) ∨ x = y := by
          first
          | (have i₁ := b2e249610
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e249610
          | exact resolve b2e249610 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e249610
        have b2e249624 : (k x x) = (k y (M.op (k x x) y)) ∨ x = y := by grind
        clear b2e249623
        have b2e249650 : (k x x) = (M.op y (M.op (k x x) y)) ∨ y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e2834 (M.op (k x x) y) y
             have i₂ := b2e249624
             grind)
          | exact superpose b2e249624 b2e2834
          | exact resolve b2e2834 b2e249624
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2834 b2e249624
        have b2e249691 : (k x x) = (M.op y (k x x)) ∨ y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e249650
             have i₂ := b2e34 (k x x) y
             grind)
          | exact superpose b2e34 b2e249650
          | exact resolve b2e249650 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e249650
        have b2e250010 : (M.op x y) = (M.op x (k x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e1169 x x y
             have i₂ := b2e249691
             grind)
          | exact superpose b2e249691 b2e1169
          | (have j0 := b2e1169 x x x
             grind)
          | exact resolve b2e1169 b2e249691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1169 b2e249691
        have b2e250033 : (M.op x y) = (M.op x (k x x)) ∨ x = (M.op x x) ∨ y = (k x x) ∨ x = y := by grind
        clear b2e250010
        have b2e250037 : y = (M.op x (k x x)) ∨ x = (M.op x x) ∨ y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e250033
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e250033
          | exact resolve b2e250033 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e250033
        have b2e250042 : x = y ∨ y = (M.op x (k x x)) ∨ y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e250037
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e250037
          | exact resolve b2e250037 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e250037
        have b2e250043 : y = (M.op x (k x x)) ∨ x = y ∨ y = (k x x) := by grind
        clear b2e250042
        have b2e250826 : y = (k x x) ∨ x = (M.op x x) ∨ x = y ∨ y = (k x x) := by
          first
          | (have i₁ := b2e248412 x
             have i₂ := b2e250043
             grind)
          | exact superpose b2e250043 b2e248412
          | (have j0 := b2e248412 x
             grind)
          | exact resolve b2e248412 b2e250043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e248412 b2e250043
        have b2e250874 : y = (k x x) ∨ x = (M.op x x) ∨ x = y := by grind
        clear b2e250826
        have b2e250884 : x = y ∨ y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e250874
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e250874
          | exact resolve b2e250874 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e250874
        have b2e250885 : y = (k x x) ∨ x = y := by grind
        clear b2e250884
        have b2e251154 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e204040 x
             have i₂ := b2e250885
             grind)
          | exact superpose b2e250885 b2e204040
          | exact resolve b2e204040 b2e250885
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e204040 b2e250885
        have b2e251376 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have r₁ := b2e251154
             have r₂ := b2e166
             grind)
          | exact resolve b2e251154 b2e166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e251154
        have b2e251431 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e251376
             have i₂ := b2e47
             grind)
          | exact superpose b2e47 b2e251376
          | exact resolve b2e251376 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e251376
        have b2e251533 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e34 (σ x) (σ x)
             have i₂ := b2e251431
             grind)
          | exact superpose b2e251431 b2e34
          | exact resolve b2e34 b2e251431
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e251431
        have b2e251610 : x = y := by
          first
          | (have r₁ := b2e251533
             have r₂ := b2e21
             grind)
          | exact resolve b2e251533 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e251533
        have b2e251695 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e166
             have i₂ := b2e251610
             grind)
          | exact superpose b2e251610 b2e166
          | exact resolve b2e166 b2e251610
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e166 b2e251610
        have b2e251859 : False := by grind
        exact b2e251859
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 (σ y))) := by
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
        have b3e34 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 (M.op X0 x)
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e64 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b3e34 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e34
          | exact resolve b3e34 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e84 : (M.op x y) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b3e34 x x
             have i₂ := b3e64
             grind)
          | exact superpose b3e64 b3e34
          | exact resolve b3e34 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e97 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e32 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e32
          | exact resolve b3e32 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e104 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e97
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e97
          | exact resolve b3e97 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97
        have b3e127 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
          first
          | (have i₁ := b3e16 (M.op x y) x
             have i₂ := b3e84
             grind)
          | exact superpose b3e84 b3e16
          | (have j0 := b3e16 (M.op x y) x
             grind)
          | (have r₁ := b3e16 (M.op x y) x
             have r₂ := b3e84
             grind)
          | exact resolve b3e16 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e131 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by grind
        clear b3e127
        have b3e132 : (M.op x y) = (k (M.op x y) x) := by
          first
          | (have j1 := b3e15 (M.op x y) x
             grind)
          | (have r₁ := b3e131
             have r₂ := b3e15 (M.op x y) x
             grind)
          | exact resolve b3e131 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e131
        have b3e168 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e53 x x
             have i₂ := b3e104
             grind)
          | exact superpose b3e104 b3e53
          | exact resolve b3e53 b3e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e104
        have b3e195 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e168
        have b3e594 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e195
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e195
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e195 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e613 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e594
        have b3e627 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e613
             have i₂ := b3e64
             grind)
          | exact superpose b3e64 b3e613
          | exact resolve b3e613 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e613
        have b3e628 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b3e627
             have r₂ := b3e23
             grind)
          | exact resolve b3e627 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e627
        have b3e629 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e628
             have i₂ := b3e64
             grind)
          | exact superpose b3e64 b3e628
          | exact resolve b3e628 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64 b3e628
        have b3e788 : x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e132
             have i₂ := b3e629
             grind)
          | exact superpose b3e629 b3e132
          | exact resolve b3e132 b3e629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132 b3e629
        have b3e902 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e195
             have i₂ := b3e788
             grind)
          | exact superpose b3e788 b3e195
          | exact resolve b3e195 b3e788
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e195 b3e788
        have b3e909 : (σ x) = (σ y) := by grind
        clear b3e902
        have b3e950 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e909
             grind)
          | exact superpose b3e909 b3e13
          | exact resolve b3e13 b3e909
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e909
        have b3e983 : x = y := by
          first
          | (have i₁ := b3e950
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e950
          | exact resolve b3e950 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e950
        have b3e1016 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e983
             grind)
          | exact superpose b3e983 b3e20
          | exact resolve b3e20 b3e983
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1017 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e983
             grind)
          | exact superpose b3e983 b3e21
          | exact resolve b3e21 b3e983
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e983
        have b3e1043 : False := by grind
        exact b3e1043
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e39 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (M.op X0 x)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e61 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e30 X0 X1
               have i₂ := b4e18 (τ X0) X1
               grind)
            | exact superpose b4e18 b4e30
            | (have j1 := b4e18 (τ X0) X1
               grind)
            | exact resolve b4e30 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e39 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e39 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e39
            | exact resolve b4e39 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e168 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) (σ X1)
               have i₂ := b4e60 X0 X1
               grind)
            | exact superpose b4e60 b4e17
            | (have j0 := b4e17 (σ X0) (σ X1)
               have j1 := b4e60 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X0) (σ X1)
               have r₂ := b4e60 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X1) (σ X0)
               have r₂ := b4e60 X0 X1
               grind)
            | exact resolve b4e17 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e172 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e175 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e168 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168
          have b4e176 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e175 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175
          have b4e183 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e176 X0 X1
               have j1 := b4e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b4e176 X0 X1
               have r₂ := b4e16 (σ X0) (σ X1)
               grind)
            | exact resolve b4e176 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e176
          have b4e191 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e183 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e183
            | (have j0 := b4e183 X0 X1
               grind)
            | exact resolve b4e183 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e183
          have b4e205 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e70
               grind)
            | exact superpose b4e70 b4e20
            | exact resolve b4e20 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e214 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e205
               have i₂ := b4e67
               grind)
            | exact superpose b4e67 b4e205
            | exact resolve b4e205 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e205
          have b4e741 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e191 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e191
            | exact resolve b4e191 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e756 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e214
               have i₂ := b4e191 x x
               grind)
            | exact superpose b4e191 b4e214
            | (have j1 := b4e191 x x
               grind)
            | exact resolve b4e214 b4e191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191
          have b4e797 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e741 X0 X1
               have i₂ := b4e30 X0 X1
               grind)
            | exact superpose b4e30 b4e741
            | (have j0 := b4e741 X0 X1
               grind)
            | exact resolve b4e741 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e741
          have b4e801 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e797 X0 X1
               have i₂ := b4e30 X0 X1
               grind)
            | exact superpose b4e30 b4e797
            | (have j0 := b4e797 X0 X1
               grind)
            | exact resolve b4e797 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e797
          have b4e907 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e61 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e61
            | exact resolve b4e61 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61
          have b4e946 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e907 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e907
            | (have j0 := b4e907 X0 X1
               grind)
            | exact resolve b4e907 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e907
          have b4e4157 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e801 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e801
            | exact resolve b4e801 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e801
          have b4e4335 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e4157 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4157
          have b4e4444 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e4335 X0 (M.op X1 X0)
               have i₂ := b4e39 X1 X0
               grind)
            | exact superpose b4e39 b4e4335
            | (have j0 := b4e4335 X0 X1
               grind)
            | exact resolve b4e4335 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e4335
          have b4e12304 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e756
               have i₂ := b4e946 x x
               grind)
            | exact superpose b4e946 b4e756
            | (have j1 := b4e946 x x
               grind)
            | (have r₁ := b4e756
               have r₂ := b4e946 x x
               grind)
            | exact resolve b4e756 b4e946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e756 b4e946
          have b4e12305 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e12304
          have b4e12306 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e12305
          have b4e12571 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e12306
               grind)
            | exact superpose b4e12306 b4e14
            | exact resolve b4e14 b4e12306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12306
          have b4e12638 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e12571
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e12571
            | exact resolve b4e12571 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12571
          have b4e12639 : x = (M.op x x) := by grind
          clear b4e12638
          have b4e12782 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b4e4444 x x
               have i₂ := b4e12639
               grind)
            | exact superpose b4e12639 b4e4444
            | (have r₁ := b4e4444 x x
               have r₂ := b4e12639
               grind)
            | exact resolve b4e4444 b4e12639
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4444
          have b4e12785 : x = (k x x) := by grind
          clear b4e12782
          have b4e13006 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e172 x x
               have i₂ := b4e12785
               grind)
            | exact superpose b4e12785 b4e172
            | (have j0 := b4e172 x x
               grind)
            | exact resolve b4e172 b4e12785
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e172 b4e12785
          have b4e13012 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e13006
          have b4e13013 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e13012
          have b4e13229 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e214
               have i₂ := b4e13013
               grind)
            | exact superpose b4e13013 b4e214
            | exact resolve b4e214 b4e13013
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214 b4e13013
          have b4e13298 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e13229
               have i₂ := b4e12639
               grind)
            | exact superpose b4e12639 b4e13229
            | exact resolve b4e13229 b4e12639
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12639 b4e13229
          have b4e13299 : False := by grind
          exact b4e13299
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b5e31 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 (k (τ X0) X1) X2
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e19
            | exact resolve b5e19 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 x)) := by
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
          have b5e35 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b5e33 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e41 : x = (M.op y y) := by
            first
            | (have i₁ := b5e37
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e37
            | exact resolve b5e37 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e42 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) := by
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
          have b5e45 : y = (M.op x y) ∨ x = (k x y) := by grind
          clear b5e42
          have b5e48 : x = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e53 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e27 X0 X1
               have i₂ := b5e18 (τ X0) X1
               grind)
            | exact superpose b5e18 b5e27
            | (have j1 := b5e18 (τ X0) X1
               grind)
            | exact resolve b5e27 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 X0 (M.op X1 (M.op X0 X2))
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (M.op X1 X0) X0
               have i₂ := b5e35 X1 X0
               grind)
            | exact superpose b5e35 b5e17
            | (have j0 := b5e17 (M.op X1 X0) X0
               grind)
            | (have r₁ := b5e17 (M.op X1 X1) X1
               have r₂ := b5e35 X1 X1
               grind)
            | exact resolve b5e17 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 (M.op X1 X0)
               have i₂ := b5e35 X1 X0
               grind)
            | exact superpose b5e35 b5e16
            | (have j0 := b5e16 X0 (M.op X1 X0)
               grind)
            | (have r₁ := b5e16 X1 (M.op X1 X1)
               have r₂ := b5e35 X1 X1
               grind)
            | exact resolve b5e16 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have j0 := b5e65 X0 X1
               have j1 := b5e16 (M.op X1 X0) X0
               grind)
            | (have r₁ := b5e65 X1 X1
               have r₂ := b5e16 (M.op X1 X1) X1
               grind)
            | exact resolve b5e65 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e101 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e32
            | exact resolve b5e32 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e128 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ X0) (M.op X2 (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X2 (σ X1)
               have i₂ := b5e52 X0 X1
               grind)
            | exact superpose b5e52 b5e13
            | (have j1 := b5e52 X0 X1
               grind)
            | exact resolve b5e13 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e130 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b5e134 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e52 X0 X1
               grind)
            | exact superpose b5e52 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e52 X0 X1
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
          have b5e137 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e52 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e139 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e137 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e137
          have b5e141 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e134 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e134
          have b5e142 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e141 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e141
          have b5e143 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e130
          have b5e147 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e142 X0 X1
               have j1 := b5e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b5e142 X0 X1
               have r₂ := b5e16 (σ X0) (σ X1)
               grind)
            | exact resolve b5e142 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e142
          have b5e148 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e143
               have r₂ := b5e23
               grind)
            | exact resolve b5e143 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e143
          have b5e153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e147 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e147
            | (have j0 := b5e147 X0 X1
               grind)
            | exact resolve b5e147 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e147
          have b5e154 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e148
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e148
            | exact resolve b5e148 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e148
          have b5e156 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e154
               grind)
            | exact superpose b5e154 b5e23
            | exact resolve b5e23 b5e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e154
          have b5e166 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e80 (k (τ X0) X1) X2
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e80
            | exact resolve b5e80 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e278 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e67 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e471 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e139 (τ X0)
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e139
            | (have j0 := b5e139 (τ X0)
               grind)
            | exact resolve b5e139 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139
          have b5e473 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e471 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e471
            | (have j0 := b5e471 X0
               grind)
            | exact resolve b5e471 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e471
          have b5e476 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e473 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e473
            | (have j0 := b5e473 X0
               grind)
            | exact resolve b5e473 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e473
          have b5e546 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e68 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68
          have b5e568 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b5e32 (M.op (σ X0) (σ X0)) X0
               have i₂ := b5e546 (σ X0)
               grind)
            | exact superpose b5e546 b5e32
            | exact resolve b5e32 b5e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e604 : ∀ X0 : G, (M.op (M.op y (M.op y X0)) y) = (M.op (M.op y (M.op y X0)) x) := by
            intro X0
            first
            | (have i₁ := b5e62 y y X0
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e62
            | exact resolve b5e62 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e647 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e153 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e153
            | exact resolve b5e153 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e694 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e647 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e647
            | (have j0 := b5e647 X0 X1
               grind)
            | exact resolve b5e647 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e647
          have b5e699 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e694 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e694
            | (have j0 := b5e694 X0 X1
               grind)
            | exact resolve b5e694 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e694
          have b5e725 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e80 (M.op (τ X0) X1) X2
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e80
            | (have j1 := b5e53 X0 X1
               grind)
            | exact resolve b5e80 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e732 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e725 X0 X1 X2
               have i₂ := b5e166 X0 X1 X2
               grind)
            | exact superpose b5e166 b5e725
            | (have j0 := b5e725 X0 X1 X2
               grind)
            | exact resolve b5e725 b5e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e166 b5e725
          have b5e1143 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ X0)) (M.op X2 (σ (τ (k X0 X1))))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e128 (τ X0) (τ X1) X2
               have i₂ := b5e101 X1 X0
               grind)
            | exact superpose b5e101 b5e128
            | (have j0 := b5e128 (τ X0) (τ X1) X2
               grind)
            | exact resolve b5e128 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128
          have b5e1175 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ X0)) (M.op X2 (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1143 X0 X1 X2
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e1143
            | (have j0 := b5e1143 X0 X1 X2
               grind)
            | exact resolve b5e1143 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1143
          have b5e1179 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1175 X0 X1 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1175
            | (have j0 := b5e1175 X0 X1 X2
               grind)
            | exact resolve b5e1175 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1175
          have b5e1181 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1179 X0 X1 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1179
            | (have j0 := b5e1179 X0 X1 X2
               grind)
            | exact resolve b5e1179 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1179
          have b5e1182 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1181 X0 X1 X2
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e1181
            | (have j0 := b5e1181 X0 X1 X2
               grind)
            | exact resolve b5e1181 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1181
          have b5e1183 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1182 X0 X0 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1182
            | (have j0 := b5e1182 X0 X1 X2
               grind)
            | exact resolve b5e1182 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1182
          have b5e1184 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X2 (k X0 X1))) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1183 X0 X1 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1183
            | (have j0 := b5e1183 X0 X1 X2
               grind)
            | exact resolve b5e1183 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1183
          have b5e2849 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e699 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e699
            | exact resolve b5e699 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2864 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e32 X0 X1
               have i₂ := b5e699 X0 X1
               grind)
            | exact superpose b5e699 b5e32
            | (have j1 := b5e699 X0 X1
               grind)
            | exact resolve b5e32 b5e699
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e699
          have b5e6643 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e568 x
               have i₂ := b5e153 x x
               grind)
            | exact superpose b5e153 b5e568
            | (have j1 := b5e153 X0 X0
               grind)
            | exact resolve b5e568 b5e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e153
          have b5e6644 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e568 x
               have i₂ := b5e52 x x
               grind)
            | exact superpose b5e52 b5e568
            | (have j1 := b5e52 X0 X0
               grind)
            | exact resolve b5e568 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e6692 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e6644 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6644
          have b5e6727 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e6692 X0
               have i₂ := b5e14 (k X0 X0)
               grind)
            | exact superpose b5e14 b5e6692
            | (have j0 := b5e6692 X0
               grind)
            | exact resolve b5e6692 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6692
          have b5e6728 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e6643 X0
               have i₂ := b5e14 (k X0 X0)
               grind)
            | exact superpose b5e14 b5e6643
            | (have j0 := b5e6643 X0
               grind)
            | exact resolve b5e6643 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6643
          have b5e9964 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e2864 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e2864
            | exact resolve b5e2864 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2864
          have b5e10057 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e9964 X0 X1
               have i₂ := b5e101 X0 X1
               grind)
            | exact superpose b5e101 b5e9964
            | (have j0 := b5e9964 X0 X1
               grind)
            | exact resolve b5e9964 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9964
          have b5e10191 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e101 X2 (k X0 X1)
               have i₂ := b5e10057 X1 X0
               grind)
            | exact superpose b5e10057 b5e101
            | (have j1 := b5e10057 X1 X0
               grind)
            | exact resolve b5e101 b5e10057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10057
          have b5e10247 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e10191 X0 X1 X2
               have i₂ := b5e101 X2 (M.op X0 X1)
               grind)
            | exact superpose b5e101 b5e10191
            | (have j0 := b5e10191 X0 X1 X2
               grind)
            | exact resolve b5e10191 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10191
          have b5e11469 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e28 X0 (k (τ X0) (τ X0))
               have i₂ := b5e6728 (τ X0)
               grind)
            | exact superpose b5e6728 b5e28
            | (have j1 := b5e6728 (τ X0)
               grind)
            | exact resolve b5e28 b5e6728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6728
          have b5e11507 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e11469 X0
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e11469
            | (have j0 := b5e11469 X0
               grind)
            | exact resolve b5e11469 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11469
          have b5e11546 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e11507 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e11507
            | (have j0 := b5e11507 X0
               grind)
            | exact resolve b5e11507 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11507
          have b5e11581 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b5e11546 X0
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e11546
            | (have j0 := b5e11546 X0
               grind)
            | exact resolve b5e11546 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e11546
          have b5e11616 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e11581 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e11581
            | (have j0 := b5e11581 X0
               grind)
            | exact resolve b5e11581 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11581
          have b5e22409 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e732 X0 (τ X0) X0
               have i₂ := b5e11616 (τ X0)
               grind)
            | exact superpose b5e11616 b5e732
            | (have j0 := b5e732 X0 (τ X0) x
               have j1 := b5e11616 (τ X0)
               grind)
            | exact resolve b5e732 b5e11616
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e732 b5e11616
          have b5e22478 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have j0 := b5e22409 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22409
          have b5e22521 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have j0 := b5e22478 X0
               have j1 := b5e476 (τ X0)
               grind)
            | (have r₁ := b5e22478 X0
               have r₂ := b5e476 (τ X0)
               grind)
            | exact resolve b5e22478 b5e476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22478
          have b5e22571 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e22521 X0
               have i₂ := b5e546 (τ X0)
               grind)
            | exact superpose b5e546 b5e22521
            | (have j0 := b5e22521 X0
               grind)
            | exact resolve b5e22521 b5e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22521
          have b5e22604 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e22571 X0
               have i₂ := b5e101 X0 X0
               grind)
            | exact superpose b5e101 b5e22571
            | (have j0 := b5e22571 X0
               grind)
            | exact resolve b5e22571 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22571
          have b5e27648 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e6727 (τ X0)
               have i₂ := b5e101 X0 X0
               grind)
            | exact superpose b5e101 b5e6727
            | (have j0 := b5e6727 (τ X0)
               grind)
            | exact resolve b5e6727 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6727
          have b5e27780 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e27648 X0
               have i₂ := b5e101 X0 (k X0 X0)
               grind)
            | exact superpose b5e101 b5e27648
            | (have j0 := b5e27648 X0
               grind)
            | exact resolve b5e27648 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27648
          have b5e27832 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e27780 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e27780
            | (have j0 := b5e27780 X0
               grind)
            | exact resolve b5e27780 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27780
          have b5e50800 : ∀ X0 X1 X2 : G, (τ (σ (k (k (τ X0) X1) X2))) = (τ (k (M.op X0 (σ X1)) (σ X2))) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e10247 X0 (σ X1) (σ X2)
               have i₂ := b5e31 X0 X1 X2
               grind)
            | exact superpose b5e31 b5e10247
            | (have j0 := b5e10247 X0 (σ X1) X2
               grind)
            | exact resolve b5e10247 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e50848 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e27832 X0
               have i₂ := b5e10247 X0 X0 X0
               grind)
            | exact superpose b5e10247 b5e27832
            | (have j0 := b5e27832 X0
               have j1 := b5e10247 X0 X0 x
               grind)
            | exact resolve b5e27832 b5e10247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10247 b5e27832
          have b5e51000 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e50848 X0
               have j1 := b5e476 X0
               grind)
            | (have r₁ := b5e50848 X0
               have r₂ := b5e476 X0
               grind)
            | exact resolve b5e50848 b5e476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e476 b5e50848
          have b5e51014 : ∀ X0 X1 X2 : G, (τ (σ (k (k (τ X0) X1) X2))) = (k (τ (M.op X0 (σ X1))) X2) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e50800 X0 X1 X2
               have i₂ := b5e32 (M.op X0 (σ X1)) X2
               grind)
            | exact superpose b5e32 b5e50800
            | (have j0 := b5e50800 X0 X1 X2
               grind)
            | exact resolve b5e50800 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e50800
          have b5e51035 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e51000 X0
               have i₂ := b5e546 X0
               grind)
            | exact superpose b5e546 b5e51000
            | (have j0 := b5e51000 X0
               grind)
            | exact resolve b5e51000 b5e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e546 b5e51000
          have b5e51039 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) X2) = (k (τ (M.op X0 (σ X1))) X2) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e51014 X0 X1 X2
               have i₂ := b5e14 (k (k (τ X0) X1) X2)
               grind)
            | exact superpose b5e14 b5e51014
            | (have j0 := b5e51014 X0 X1 X2
               grind)
            | exact resolve b5e51014 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51014
          have b5e51431 : ∀ X0 X1 : G, (τ (k (k X0 X0) X1)) = (k (τ (M.op X0 X0)) (τ X1)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e101 X1 (k X0 X0)
               have i₂ := b5e51035 X0
               grind)
            | exact superpose b5e51035 b5e101
            | (have j1 := b5e51035 X0
               grind)
            | exact resolve b5e101 b5e51035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51035
          have b5e51549 : ∀ X0 X1 : G, (τ (k (k X0 X0) X1)) = (τ (k (M.op X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e51431 X0 X1
               have i₂ := b5e101 X1 (M.op X0 X0)
               grind)
            | exact superpose b5e101 b5e51431
            | (have j0 := b5e51431 X0 X1
               grind)
            | exact resolve b5e51431 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101 b5e51431
          have b5e77803 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e35 (τ X0) (τ X0)
               have i₂ := b5e22604 X0
               grind)
            | exact superpose b5e22604 b5e35
            | (have j1 := b5e22604 X0
               grind)
            | exact resolve b5e35 b5e22604
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22604
          have b5e90464 : ∀ X0 X1 : G, (k (k X0 X0) X1) = (σ (τ (k (M.op X0 X0) X1))) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e15 (k (k X0 X0) X1)
               have i₂ := b5e51549 X0 X1
               grind)
            | exact superpose b5e51549 b5e15
            | (have j1 := b5e51549 X0 X1
               grind)
            | exact resolve b5e15 b5e51549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51549
          have b5e90537 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (k (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e90464 X0 X1
               have i₂ := b5e15 (k (M.op X0 X0) X1)
               grind)
            | exact superpose b5e15 b5e90464
            | (have j0 := b5e90464 X0 X1
               grind)
            | exact resolve b5e90464 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90464
          have b5e203551 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e568 X0
               have i₂ := b5e51039 (σ X0) X0 X0
               grind)
            | exact superpose b5e51039 b5e568
            | (have j1 := b5e51039 (σ X0) X0 x
               grind)
            | exact resolve b5e568 b5e51039
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e568 b5e51039
          have b5e203585 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (k X0 X0) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e203551 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e203551
            | (have j0 := b5e203551 X0
               grind)
            | exact resolve b5e203551 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e203551
          have b5e203594 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e203585 X0
               have i₂ := b5e19 X0 X0
               grind)
            | exact superpose b5e19 b5e203585
            | (have j0 := b5e203585 X0
               grind)
            | exact resolve b5e203585 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e203585
          have b5e203814 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e15 (M.op (σ X0) (σ X0))
               have i₂ := b5e203594 X0
               grind)
            | exact superpose b5e203594 b5e15
            | (have j1 := b5e203594 X0
               grind)
            | exact resolve b5e15 b5e203594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e203594
          have b5e248717 : ∀ X0 : G, (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e77803 (σ X0)
               have i₂ := b5e80 X0 (σ X0)
               grind)
            | exact superpose b5e80 b5e77803
            | (have j0 := b5e77803 (σ X0)
               grind)
            | exact resolve b5e77803 b5e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80 b5e77803
          have b5e248732 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e248717 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e248717
            | (have j0 := b5e248717 X0
               grind)
            | exact resolve b5e248717 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248717
          have b5e248736 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e248732 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e248732
            | (have j0 := b5e248732 X0
               grind)
            | exact resolve b5e248732 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248732
          have b5e248801 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e35 X0 (k X0 X0)
               have i₂ := b5e248736 X0
               grind)
            | exact superpose b5e248736 b5e35
            | (have j1 := b5e248736 X0
               grind)
            | exact resolve b5e35 b5e248736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e248865 : (M.op (M.op y (k y y)) y) = (M.op (M.op y (k y y)) x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e604 (k y y)
               have i₂ := b5e248736 y
               grind)
            | exact superpose b5e248736 b5e604
            | (have j1 := b5e248736 y
               grind)
            | exact resolve b5e604 b5e248736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e604
          have b5e248934 : (M.op (M.op y (k y y)) y) = (M.op (M.op y (k y y)) x) ∨ x = y := by
            first
            | (have i₁ := b5e248865
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e248865
            | exact resolve b5e248865 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248865
          have b5e249371 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e278 (k X0 X0)
               have i₂ := b5e248801 X0
               grind)
            | exact superpose b5e248801 b5e278
            | (have j1 := b5e248801 X0
               grind)
            | exact resolve b5e278 b5e248801
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e278 b5e248801
          have b5e249550 : (M.op (k y y) x) = (M.op (k y y) y) ∨ x = y ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e248934
               have i₂ := b5e248736 y
               grind)
            | exact superpose b5e248736 b5e248934
            | (have j1 := b5e248736 y
               grind)
            | exact resolve b5e248934 b5e248736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248934
          have b5e249557 : x = y ∨ (M.op (k y y) x) = (M.op (k y y) y) ∨ x = y := by
            first
            | (have i₁ := b5e249550
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e249550
            | exact resolve b5e249550 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e249550
          have b5e249558 : (M.op (k y y) x) = (M.op (k y y) y) ∨ x = y := by grind
          clear b5e249557
          have b5e249816 : (k y y) = (k (k y y) (M.op (k y y) x)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b5e249371 y
               have i₂ := b5e249558
               grind)
            | exact superpose b5e249558 b5e249371
            | (have j0 := b5e249371 y
               grind)
            | exact resolve b5e249371 b5e249558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e249371 b5e249558
          have b5e249838 : x = y ∨ (k y y) = (k (k y y) (M.op (k y y) x)) ∨ x = y := by
            first
            | (have i₁ := b5e249816
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e249816
            | exact resolve b5e249816 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e249816
          have b5e249839 : (k y y) = (k (k y y) (M.op (k y y) x)) ∨ x = y := by grind
          clear b5e249838
          have b5e249875 : (k y y) = (k (M.op y y) (M.op (k y y) x)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b5e90537 y (M.op (k y y) x)
               have i₂ := b5e249839
               grind)
            | exact superpose b5e249839 b5e90537
            | (have j0 := b5e90537 y x
               grind)
            | exact resolve b5e90537 b5e249839
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90537 b5e249839
          have b5e249886 : (k y y) = (k x (M.op (k y y) x)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b5e249875
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e249875
            | exact resolve b5e249875 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e249875
          have b5e249899 : x = y ∨ (k y y) = (k x (M.op (k y y) x)) ∨ x = y := by
            first
            | (have i₁ := b5e249886
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e249886
            | exact resolve b5e249886 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e249886
          have b5e249900 : (k y y) = (k x (M.op (k y y) x)) ∨ x = y := by grind
          clear b5e249899
          have b5e249993 : (k y y) = (M.op x (M.op (k y y) x)) ∨ x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e2849 (M.op (k y y) x) x
               have i₂ := b5e249900
               grind)
            | exact superpose b5e249900 b5e2849
            | exact resolve b5e2849 b5e249900
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2849 b5e249900
          have b5e250034 : (k y y) = (M.op x (k y y)) ∨ x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e249993
               have i₂ := b5e35 (k y y) x
               grind)
            | exact superpose b5e35 b5e249993
            | exact resolve b5e249993 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e249993
          have b5e250388 : (M.op y x) = (M.op y (k y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e1184 y y x
               have i₂ := b5e250034
               grind)
            | exact superpose b5e250034 b5e1184
            | (have j0 := b5e1184 y y x
               grind)
            | exact resolve b5e1184 b5e250034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1184 b5e250034
          have b5e250411 : (M.op y x) = (M.op y (k y y)) ∨ y = (M.op y y) ∨ x = (k y y) ∨ x = y := by grind
          clear b5e250388
          have b5e250415 : x = (M.op y (k y y)) ∨ y = (M.op y y) ∨ x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e250411
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e250411
            | exact resolve b5e250411 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e250411
          have b5e250421 : x = y ∨ x = (M.op y (k y y)) ∨ x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e250415
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e250415
            | exact resolve b5e250415 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e250415
          have b5e250422 : x = (M.op y (k y y)) ∨ x = y ∨ x = (k y y) := by grind
          clear b5e250421
          have b5e251127 : x = (k y y) ∨ y = (M.op y y) ∨ x = y ∨ x = (k y y) := by
            first
            | (have i₁ := b5e248736 y
               have i₂ := b5e250422
               grind)
            | exact superpose b5e250422 b5e248736
            | (have j0 := b5e248736 y
               grind)
            | exact resolve b5e248736 b5e250422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248736 b5e250422
          have b5e251175 : x = (k y y) ∨ y = (M.op y y) ∨ x = y := by grind
          clear b5e251127
          have b5e251185 : x = y ∨ x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e251175
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e251175
            | exact resolve b5e251175 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e251175
          have b5e251186 : x = (k y y) ∨ x = y := by grind
          clear b5e251185
          have b5e251461 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e203814 y
               have i₂ := b5e251186
               grind)
            | exact superpose b5e251186 b5e203814
            | exact resolve b5e203814 b5e251186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e203814 b5e251186
          have b5e251683 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have r₁ := b5e251461
               have r₂ := b5e156
               grind)
            | exact resolve b5e251461 b5e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e251461
          have b5e251738 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e251683
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e251683
            | exact resolve b5e251683 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e251683
          have b5e251843 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e35 (σ y) (σ y)
               have i₂ := b5e251738
               grind)
            | exact superpose b5e251738 b5e35
            | exact resolve b5e35 b5e251738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e251738
          have b5e251920 : x = y := by
            first
            | (have r₁ := b5e251843
               have r₂ := b5e24
               grind)
            | exact resolve b5e251843 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e251843
          have b5e252012 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e156
               have i₂ := b5e251920
               grind)
            | exact superpose b5e251920 b5e156
            | exact resolve b5e156 b5e251920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e156 b5e251920
          have b5e252178 : False := by grind
          exact b5e252178
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
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
        have b6e35 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 (σ y))) := by
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
        have b6e37 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op X0 x)
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e54 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
        have b6e59 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e54
             have r₂ := b6e21
             grind)
          | exact resolve b6e54 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e63 : x = (M.op x y) := by
          first
          | (have r₁ := b6e59
             have r₂ := b6e20
             grind)
          | exact resolve b6e59 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e79 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e63
             grind)
          | exact superpose b6e63 b6e23
          | exact resolve b6e23 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e80 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e63
             grind)
          | exact superpose b6e63 b6e20
          | exact resolve b6e20 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e102 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e35 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e35
          | exact resolve b6e35 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e109 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e102
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e102
          | exact resolve b6e102 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102
        have b6e220 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e53 x x
             have i₂ := b6e109
             grind)
          | exact superpose b6e109 b6e53
          | exact resolve b6e53 b6e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53 b6e109
        have b6e227 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e220
        have b6e230 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e227
             have r₂ := b6e79
             grind)
          | exact resolve b6e227 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79 b6e227
        have b6e251 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e230
             grind)
          | exact superpose b6e230 b6e13
          | exact resolve b6e13 b6e230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e230
        have b6e263 : y = (k x x) := by
          first
          | (have i₁ := b6e251
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e251
          | exact resolve b6e251 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e251
        have b6e288 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e263
             grind)
          | exact superpose b6e263 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e263
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e289 : x = (M.op x x) ∨ y = (M.op x x) := by grind
        clear b6e288
        have b6e350 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e15 x x
             have i₂ := b6e289
             grind)
          | exact superpose b6e289 b6e15
          | (have j0 := b6e15 x x
             grind)
          | (have r₁ := b6e15 x x
             have r₂ := b6e289
             grind)
          | exact resolve b6e15 b6e289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e289
        have b6e355 : x = (k x x) ∨ y = (M.op x x) := by grind
        clear b6e350
        have b6e356 : x = y ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e355
             have i₂ := b6e263
             grind)
          | exact superpose b6e263 b6e355
          | exact resolve b6e355 b6e263
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e263 b6e355
        have b6e357 : y = (M.op x x) := by
          first
          | (have r₁ := b6e356
             have r₂ := b6e80
             grind)
          | exact resolve b6e356 b6e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80 b6e356
        have b6e391 : y = (M.op x y) := by
          first
          | (have i₁ := b6e37 x x
             have i₂ := b6e357
             grind)
          | exact superpose b6e357 b6e37
          | exact resolve b6e37 b6e357
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37 b6e357
        have b6e402 : False := by grind
        exact b6e402
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
          have b7e36 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
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
          have b7e38 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (M.op X1 X0) X0
               have i₂ := b7e38 X1 X0
               grind)
            | exact superpose b7e38 b7e17
            | (have j0 := b7e17 (M.op X1 X0) X0
               grind)
            | (have r₁ := b7e17 (M.op X1 X1) X1
               have r₂ := b7e38 X1 X1
               grind)
            | exact resolve b7e17 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have j0 := b7e48 X0 X1
               have j1 := b7e16 (M.op X1 X0) X0
               grind)
            | (have r₁ := b7e48 X1 X1
               have r₂ := b7e16 (M.op X1 X1) X1
               grind)
            | exact resolve b7e48 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e64 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
          have b7e67 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e21
               grind)
            | exact resolve b7e64 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e71 : y = (M.op y x) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e22
               grind)
            | exact resolve b7e67 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e85 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e22
            | exact resolve b7e22 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e98 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e36 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e105 : (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e98
            | exact resolve b7e98 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e180 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X0) (σ X1)
               have i₂ := b7e62 X0 X1
               grind)
            | exact superpose b7e62 b7e17
            | (have j0 := b7e17 (σ X0) (σ X1)
               have j1 := b7e62 X0 X1
               grind)
            | (have r₁ := b7e17 (σ X0) (σ X1)
               have r₂ := b7e62 X0 X1
               grind)
            | (have r₁ := b7e17 (σ X1) (σ X0)
               have r₂ := b7e62 X0 X1
               grind)
            | exact resolve b7e17 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e188 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e180 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e180
          have b7e189 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e188 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e188
          have b7e193 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e189 X0 X1
               have j1 := b7e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b7e189 X0 X1
               have r₂ := b7e16 (σ X0) (σ X1)
               grind)
            | exact resolve b7e189 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e189
          have b7e216 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e193 X0 X1
               have i₂ := b7e19 X0 X1
               grind)
            | exact superpose b7e19 b7e193
            | (have j0 := b7e193 X0 X1
               grind)
            | exact resolve b7e193 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e193
          have b7e219 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e62 y y
               have i₂ := b7e105
               grind)
            | exact superpose b7e105 b7e62
            | exact resolve b7e62 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e226 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e219
          have b7e804 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b7e105
               have i₂ := b7e216 y y
               grind)
            | exact superpose b7e216 b7e105
            | (have j1 := b7e216 y y
               grind)
            | exact resolve b7e105 b7e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105 b7e216
          have b7e1131 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y y)) := by grind
          clear b7e804
          have b7e1137 : (σ x) = (σ (k y y)) := by
            first
            | (have r₁ := b7e1131
               have r₂ := b7e226
               grind)
            | exact resolve b7e1131 b7e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e226 b7e1131
          have b7e1251 : (τ (σ x)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1137
               grind)
            | exact superpose b7e1137 b7e14
            | exact resolve b7e14 b7e1137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1137
          have b7e1288 : x = (k y y) := by
            first
            | (have i₁ := b7e1251
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1251
            | exact resolve b7e1251 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1251
          have b7e1359 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e1288
               grind)
            | exact superpose b7e1288 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e1288
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1360 : y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b7e1359
          have b7e1402 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e50 y y
               have i₂ := b7e1360
               grind)
            | exact superpose b7e1360 b7e50
            | exact resolve b7e50 b7e1360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50 b7e1360
          have b7e1405 : y = (k y y) ∨ x = (M.op y y) := by grind
          clear b7e1402
          have b7e1410 : x = y ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e1405
               have i₂ := b7e1288
               grind)
            | exact superpose b7e1288 b7e1405
            | exact resolve b7e1405 b7e1288
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1288 b7e1405
          have b7e1417 : x = (M.op y y) := by
            first
            | (have r₁ := b7e1410
               have r₂ := b7e85
               grind)
            | exact resolve b7e1410 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e1410
          have b7e1505 : x = (M.op y x) := by
            first
            | (have i₁ := b7e38 y y
               have i₂ := b7e1417
               grind)
            | exact superpose b7e1417 b7e38
            | exact resolve b7e38 b7e1417
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e1417
          have b7e1522 : False := by grind
          exact b7e1522
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
          have b8e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e105 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e118 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e105
          have b8e123 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e118
               have r₂ := b8e23
               grind)
            | exact resolve b8e118 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e129 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e123
               grind)
            | exact superpose b8e123 b8e20
            | exact resolve b8e20 b8e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e226 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e129
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e129
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e129 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e227 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e226
          have b8e228 : y = (M.op x y) := by
            first
            | (have r₁ := b8e227
               have r₂ := b8e22
               grind)
            | exact resolve b8e227 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e227
          have b8e229 : False := by grind
          exact b8e229

/-- `Equation3320`: `x ◇ y = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_x_pxy_Equation3320 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3320 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3320.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
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
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
        have b1e37 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
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
        have b1e38 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e38 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e38
          | exact resolve b1e38 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e43 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e37 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e37
          | exact resolve b1e37 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e89 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
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
        have b1e179 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (σ X0) (σ X1)
             have i₂ := b1e59 X0 X1
             grind)
          | exact superpose b1e59 b1e16
          | (have j0 := b1e16 (σ X0) (σ X1)
             have j1 := b1e59 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X0) (σ X1)
             have r₂ := b1e59 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X1) (σ X0)
             have r₂ := b1e59 X0 X1
             grind)
          | exact resolve b1e16 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e187 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e179 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e179
        have b1e188 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e187 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e187
        have b1e197 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e188 X0 X1
             have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b1e188 X0 X1
             have r₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e188 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e188
        have b1e209 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e197 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e197
          | (have j0 := b1e197 X0 X1
             grind)
          | exact resolve b1e197 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e197
        have b1e822 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e42 (σ X0)
             have i₂ := b1e209 X0 x
             grind)
          | exact superpose b1e209 b1e42
          | (have j1 := b1e209 X0 x
             grind)
          | exact resolve b1e42 b1e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e209
        have b1e1217 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e89 (σ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e89
          | exact resolve b1e89 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89
        have b1e1260 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e1217 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e1217
          | (have j0 := b1e1217 X0 X1
             grind)
          | exact resolve b1e1217 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1217
        have b1e6553 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e822 x
             grind)
          | exact superpose b1e822 b1e21
          | (have j1 := b1e822 x
             grind)
          | exact resolve b1e21 b1e822
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e822
        have b1e8037 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e6553
             have i₂ := b1e1260 x x
             grind)
          | exact superpose b1e1260 b1e6553
          | (have j1 := b1e1260 x x
             grind)
          | exact resolve b1e6553 b1e1260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1260 b1e6553
        have b1e8038 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e8037
        have b1e8040 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e8038
             have i₂ := b1e43 x
             grind)
          | exact superpose b1e43 b1e8038
          | exact resolve b1e8038 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8038
        have b1e8043 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e8040
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8040
          | exact resolve b1e8040 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8040
        have b1e8044 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e8043
        have b1e8049 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e8044
             have i₂ := b1e43 x
             grind)
          | exact superpose b1e43 b1e8044
          | exact resolve b1e8044 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8044
        have b1e8052 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e8049
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8049
          | exact resolve b1e8049 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8049
        have b1e8055 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e8052
             have i₂ := b1e43 x
             grind)
          | exact superpose b1e43 b1e8052
          | exact resolve b1e8052 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e8052
        have b1e8057 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e8055
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8055
          | exact resolve b1e8055 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8055
        have b1e8347 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e8057
             grind)
          | exact superpose b1e8057 b1e13
          | exact resolve b1e13 b1e8057
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8057
        have b1e8428 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e8347
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e8347
          | exact resolve b1e8347 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8347
        have b1e8429 : x = y := by grind
        clear b1e8428
        have b1e8718 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e8429
             grind)
          | exact superpose b1e8429 b1e21
          | exact resolve b1e21 b1e8429
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e8719 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e8429
             grind)
          | exact superpose b1e8429 b1e22
          | exact resolve b1e22 b1e8429
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8429
        have b1e8754 : False := by grind
        exact b1e8754
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
        have b2e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
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
        have b2e34 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op X0 x)
             have i₂ := b2e12 X0 X0 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e32 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e32
          | exact resolve b2e32 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e39 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
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
        have b2e42 : x = (M.op y x) ∨ y = (k y x) := by grind
        clear b2e39
        have b2e45 : y = (k y x) := by
          first
          | (have j1 := b2e15 y x
             grind)
          | (have r₁ := b2e42
             have r₂ := b2e15 y x
             grind)
          | exact resolve b2e42 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e59 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 (M.op X1 X1)
             have i₂ := b2e34 X1 X0
             grind)
          | exact superpose b2e34 b2e15
          | (have j0 := b2e15 X0 (M.op X1 X1)
             grind)
          | (have r₁ := b2e15 X1 (M.op X1 X1)
             have r₂ := b2e34 X1 X1
             grind)
          | exact resolve b2e15 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e70 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e27 X1 X0
             grind)
          | exact superpose b2e27 b2e13
          | exact resolve b2e13 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e31
          | exact resolve b2e31 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X0 X1
             have i₂ := b2e17 X0 (σ X1)
             grind)
          | exact superpose b2e17 b2e31
          | (have j1 := b2e17 X0 (σ X1)
             grind)
          | exact resolve b2e31 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e129 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e49 y x
             grind)
          | exact superpose b2e49 b2e21
          | (have j1 := b2e49 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e49 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e49 x y
             grind)
          | exact resolve b2e21 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e132 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X0) (σ X1)
             have i₂ := b2e49 X0 X1
             grind)
          | exact superpose b2e49 b2e16
          | (have j0 := b2e16 (σ X0) (σ X1)
             have j1 := b2e49 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X0) (σ X1)
             have r₂ := b2e49 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X1) (σ X0)
             have r₂ := b2e49 X0 X1
             grind)
          | exact resolve b2e16 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e138 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e49 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e140 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e132 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e132
        have b2e141 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e140 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e140
        have b2e143 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e129
        have b2e147 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e141 X0 X1
             have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b2e141 X0 X1
             have r₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e141 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e141
        have b2e149 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e143
             have r₂ := b2e22
             grind)
          | exact resolve b2e143 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e143
        have b2e154 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e147 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e147
          | (have j0 := b2e147 X0 X1
             grind)
          | exact resolve b2e147 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e147
        have b2e155 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e149
             have i₂ := b2e45
             grind)
          | exact superpose b2e45 b2e149
          | exact resolve b2e149 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45 b2e149
        have b2e156 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e155
             grind)
          | exact superpose b2e155 b2e22
          | exact resolve b2e22 b2e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e155
        have b2e409 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e59 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e442 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e70 X0 (M.op (σ X0) (σ X0))
             have i₂ := b2e409 (σ X0)
             grind)
          | exact superpose b2e409 b2e70
          | exact resolve b2e70 b2e409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e409
        have b2e446 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e442 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e442
          | exact resolve b2e442 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e442
        have b2e751 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e154 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e154
          | exact resolve b2e154 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e764 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 (σ X0) X1
             have i₂ := b2e154 X0 X0
             grind)
          | exact superpose b2e154 b2e34
          | (have j1 := b2e154 X0 X0
             grind)
          | exact resolve b2e34 b2e154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e154
        have b2e792 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e751 X0 X1
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e751
          | (have j0 := b2e751 X0 X1
             grind)
          | exact resolve b2e751 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e751
        have b2e795 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e792 X0 X1
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e792
          | (have j0 := b2e792 X0 X1
             grind)
          | exact resolve b2e792 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e792
        have b2e1118 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e138 (τ X0) (τ X1)
             have i₂ := b2e73 X1 X0
             grind)
          | exact superpose b2e73 b2e138
          | (have j0 := b2e138 (τ X0) (τ X1)
             grind)
          | exact resolve b2e138 b2e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e138
        have b2e1127 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1118 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e1118
          | (have j0 := b2e1118 X0 X1
             grind)
          | exact resolve b2e1118 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1118
        have b2e1132 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1127 X0 X1
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e1127
          | (have j0 := b2e1127 X0 X1
             grind)
          | exact resolve b2e1127 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1127
        have b2e1136 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1132 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1132
          | (have j0 := b2e1132 X0 X1
             grind)
          | exact resolve b2e1132 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1132
        have b2e1139 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1136 X0 X1
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e1136
          | (have j0 := b2e1136 X0 X1
             grind)
          | exact resolve b2e1136 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1136
        have b2e1140 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e1139 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1139
          | (have j0 := b2e1139 X0 X1
             grind)
          | exact resolve b2e1139 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1139
        have b2e1141 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e1140 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1140
          | (have j0 := b2e1140 X0 X1
             grind)
          | exact resolve b2e1140 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1140
        have b2e3528 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e795 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e795
          | exact resolve b2e795 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e795
        have b2e3729 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (k (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e70 X0 X1
             have i₂ := b2e3528 X1 (σ X0)
             grind)
          | exact superpose b2e3528 b2e70
          | (have j1 := b2e3528 X1 (σ X0)
             grind)
          | exact resolve b2e70 b2e3528
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70 b2e3528
        have b2e113326 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (k X0 (τ x)) ∨ (σ X0) = (k (σ X0) x) := by
          intro X0
          first
          | (have i₁ := b2e3729 X0 x
             have i₂ := b2e36 (σ X0)
             grind)
          | exact superpose b2e36 b2e3729
          | (have j0 := b2e3729 X0 x
             grind)
          | exact resolve b2e3729 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3729
        have b2e120273 : ∀ X0 : G, (k (τ X0) (τ x)) = (τ (M.op X0 y)) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e113326 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e113326
          | exact resolve b2e113326 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e113326
        have b2e120347 : ∀ X0 : G, (τ (k X0 x)) = (τ (M.op X0 y)) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e120273 X0
             have i₂ := b2e73 x X0
             grind)
          | exact superpose b2e73 b2e120273
          | (have j0 := b2e120273 X0
             grind)
          | exact resolve b2e120273 b2e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73 b2e120273
        have b2e120730 : ∀ X0 : G, (k X0 x) = (σ (τ (M.op X0 y))) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e14 (k X0 x)
             have i₂ := b2e120347 X0
             grind)
          | exact superpose b2e120347 b2e14
          | (have j1 := b2e120347 X0
             grind)
          | exact resolve b2e14 b2e120347
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120347
        have b2e120809 : ∀ X0 : G, (M.op X0 y) = (k X0 x) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e120730 X0
             have i₂ := b2e14 (M.op X0 y)
             grind)
          | exact superpose b2e14 b2e120730
          | (have j0 := b2e120730 X0
             grind)
          | exact resolve b2e120730 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120730
        have b2e121228 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by
          intro X0
          first
          | (have i₁ := b2e764 x x
             have i₂ := b2e120809 x
             grind)
          | exact superpose b2e120809 b2e764
          | (have j1 := b2e120809 x
             grind)
          | exact resolve b2e764 b2e120809
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e764 b2e120809
        have b2e121467 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by
          intro X0
          first
          | (have i₁ := b2e121228 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e121228
          | exact resolve b2e121228 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121228
        have b2e121508 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (k x x) := by
          intro X0
          first
          | (have i₁ := b2e121467 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e121467
          | (have j0 := b2e121467 X0
             grind)
          | exact resolve b2e121467 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121467
        have b2e121519 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (k x x) := by
          intro X0
          first
          | (have j0 := b2e121508 X0
             grind)
          | (have r₁ := b2e121508 X0
             have r₂ := b2e156
             grind)
          | exact resolve b2e121508 b2e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121508
        have b2e121938 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e446 x
             have i₂ := b2e121519 (σ x)
             grind)
          | exact superpose b2e121519 b2e446
          | exact resolve b2e446 b2e121519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e446 b2e121519
        have b2e122713 : x = (k x (k (τ (σ x)) y)) ∨ x = (k x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e121938
             have i₂ := b2e76 (σ x) y
             grind)
          | exact superpose b2e76 b2e121938
          | (have j1 := b2e76 (σ x) y
             grind)
          | exact resolve b2e121938 b2e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76 b2e121938
        have b2e122725 : x = (k x (k (τ (σ x)) y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e122713
             have r₂ := b2e22
             grind)
          | exact resolve b2e122713 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122713
        have b2e122735 : x = (k x (k (τ (σ x)) y)) ∨ x = (k x x) := by
          first
          | (have r₁ := b2e122725
             have r₂ := b2e21
             grind)
          | exact resolve b2e122725 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122725
        have b2e122746 : x = (k x (k x y)) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e122735
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e122735
          | exact resolve b2e122735 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122735
        have b2e122753 : x = (k x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e122746
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e122746
          | exact resolve b2e122746 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e122746
        have b2e122754 : x = (k x x) := by grind
        clear b2e122753
        have b2e123197 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1141 x x
             have i₂ := b2e122754
             grind)
          | exact superpose b2e122754 b2e1141
          | (have j0 := b2e1141 x x
             grind)
          | (have r₁ := b2e1141 x x
             have r₂ := b2e122754
             grind)
          | exact resolve b2e1141 b2e122754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1141 b2e122754
        have b2e123198 : x ≠ x ∨ x = (M.op x x) := by grind
        clear b2e123197
        have b2e123199 : x = (M.op x x) := by grind
        clear b2e123198
        have b2e123214 : x = (M.op x y) := by
          first
          | (have i₁ := b2e123199
             have i₂ := b2e36 x
             grind)
          | exact superpose b2e36 b2e123199
          | exact resolve b2e123199 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e123199
        have b2e123228 : x = y := by
          first
          | (have i₁ := b2e123214
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e123214
          | exact resolve b2e123214 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123214
        have b2e123593 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e156
             have i₂ := b2e123228
             grind)
          | exact superpose b2e123228 b2e156
          | exact resolve b2e156 b2e123228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e156 b2e123228
        have b2e123685 : False := by grind
        exact b2e123685
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
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
        have b3e36 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e32 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e32
          | exact resolve b3e32 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e37 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e31
          | exact resolve b3e31 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e62 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e15 X0 x
             have i₂ := b3e37 X0
             grind)
          | exact superpose b3e37 b3e15
          | (have j0 := b3e15 X0 x
             grind)
          | exact resolve b3e15 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e180 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e55 X0 x
             have i₂ := b3e36 (σ X0)
             grind)
          | exact superpose b3e36 b3e55
          | (have j0 := b3e55 X0 x
             grind)
          | exact resolve b3e55 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e1742 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e36 (σ x)
             have i₂ := b3e180 x
             grind)
          | exact superpose b3e180 b3e36
          | (have j1 := b3e180 x
             grind)
          | exact resolve b3e36 b3e180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e180
        have b3e1766 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by grind
        clear b3e1742
        have b3e1780 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e1766
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1766
          | exact resolve b3e1766 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1766
        have b3e1799 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1780
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1780
          | exact resolve b3e1780 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1780
        have b3e1808 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1799
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e1799
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e1799 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1841 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e1808
        have b3e1855 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1841
             have i₂ := b3e37 x
             grind)
          | exact superpose b3e37 b3e1841
          | exact resolve b3e1841 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1841
        have b3e1856 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b3e1855
             have r₂ := b3e23
             grind)
          | exact resolve b3e1855 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e1855
        have b3e1857 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1856
             have i₂ := b3e37 x
             grind)
          | exact superpose b3e37 b3e1856
          | exact resolve b3e1856 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e1856
        have b3e2030 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e62 x
             have i₂ := b3e1857
             grind)
          | exact superpose b3e1857 b3e62
          | (have j0 := b3e62 x
             grind)
          | (have r₁ := b3e62 x
             have r₂ := b3e1857
             grind)
          | exact resolve b3e62 b3e1857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62 b3e1857
        have b3e2039 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e2030
        have b3e2234 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1799
             have i₂ := b3e2039
             grind)
          | exact superpose b3e2039 b3e1799
          | exact resolve b3e1799 b3e2039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1799 b3e2039
        have b3e2246 : (σ x) = (σ y) := by grind
        clear b3e2234
        have b3e2371 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e2246
             grind)
          | exact superpose b3e2246 b3e13
          | exact resolve b3e13 b3e2246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2246
        have b3e2419 : x = y := by
          first
          | (have i₁ := b3e2371
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e2371
          | exact resolve b3e2371 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2371
        have b3e2629 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e2419
             grind)
          | exact superpose b3e2419 b3e20
          | exact resolve b3e20 b3e2419
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2630 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e2419
             grind)
          | exact superpose b3e2419 b3e21
          | exact resolve b3e21 b3e2419
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2419
        have b3e2655 : False := by grind
        exact b3e2655
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e36 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
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
          have b4e37 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
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
          have b4e41 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e37
            | exact resolve b4e37 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e42 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
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
          have b4e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e79 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
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
          have b4e81 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e79
               have i₂ := b4e42 x
               grind)
            | exact superpose b4e42 b4e79
            | exact resolve b4e79 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e79
          have b4e168 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) (σ X1)
               have i₂ := b4e60 X0 X1
               grind)
            | exact superpose b4e60 b4e17
            | (have j0 := b4e17 (σ X0) (σ X1)
               have j1 := b4e60 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X0) (σ X1)
               have r₂ := b4e60 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X1) (σ X0)
               have r₂ := b4e60 X0 X1
               grind)
            | exact resolve b4e17 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e174 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e176 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e168 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168
          have b4e177 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e176 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e176
          have b4e183 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e177 X0 X1
               have j1 := b4e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b4e177 X0 X1
               have r₂ := b4e16 (σ X0) (σ X1)
               grind)
            | exact resolve b4e177 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e177
          have b4e191 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e183 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e183
            | (have j0 := b4e183 X0 X1
               grind)
            | exact resolve b4e183 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e183
          have b4e863 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e191 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e191
            | exact resolve b4e191 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e874 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e81
               have i₂ := b4e191 x x
               grind)
            | exact superpose b4e191 b4e81
            | (have j1 := b4e191 x x
               grind)
            | exact resolve b4e81 b4e191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191
          have b4e914 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e863 X0 X1
               have i₂ := b4e30 X0 X1
               grind)
            | exact superpose b4e30 b4e863
            | (have j0 := b4e863 X0 X1
               grind)
            | exact resolve b4e863 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e863
          have b4e918 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e914 X0 X1
               have i₂ := b4e30 X0 X1
               grind)
            | exact superpose b4e30 b4e914
            | (have j0 := b4e914 X0 X1
               grind)
            | exact resolve b4e914 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e914
          have b4e4416 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e918 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e918
            | exact resolve b4e918 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e918
          have b4e4658 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e4416 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4416
          have b4e4754 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e874
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e874
            | (have j1 := b4e18 x x
               grind)
            | exact resolve b4e874 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e874
          have b4e4755 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e4754
          have b4e4756 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e4755
          have b4e4877 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e4756
               grind)
            | exact superpose b4e4756 b4e14
            | exact resolve b4e14 b4e4756
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4756
          have b4e4942 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e4877
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e4877
            | exact resolve b4e4877 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4877
          have b4e4943 : x = (M.op x x) := by grind
          clear b4e4942
          have b4e5145 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b4e4658 x x
               have i₂ := b4e4943
               grind)
            | exact superpose b4e4943 b4e4658
            | (have j0 := b4e4658 x x
               grind)
            | (have r₁ := b4e4658 x x
               have r₂ := b4e4943
               grind)
            | exact resolve b4e4658 b4e4943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4658
          have b4e5146 : x = (k x x) := by grind
          clear b4e5145
          have b4e5814 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e174 x x
               have i₂ := b4e5146
               grind)
            | exact superpose b4e5146 b4e174
            | (have j0 := b4e174 x x
               grind)
            | exact resolve b4e174 b4e5146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e174 b4e5146
          have b4e5815 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e5814
          have b4e5816 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e5815
          have b4e5951 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e81
               have i₂ := b4e5816
               grind)
            | exact superpose b4e5816 b4e81
            | exact resolve b4e81 b4e5816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81 b4e5816
          have b4e6014 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e5951
               have i₂ := b4e4943
               grind)
            | exact superpose b4e4943 b4e5951
            | exact resolve b4e5951 b4e4943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4943 b4e5951
          have b4e6015 : False := by grind
          exact b4e6015
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b5e33 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
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
          have b5e35 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op X0 x)
               have i₂ := b5e13 X0 X0 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
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
          have b5e41 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) := by
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
          have b5e44 : y = (M.op x y) ∨ x = (k x y) := by grind
          clear b5e41
          have b5e47 : x = (k x y) := by
            first
            | (have r₁ := b5e44
               have r₂ := b5e21
               grind)
            | exact resolve b5e44 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e72 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e131 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e51 x y
               grind)
            | exact superpose b5e51 b5e24
            | (have j1 := b5e51 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e51 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e51 y x
               grind)
            | exact resolve b5e24 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e134 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e51 X0 X1
               grind)
            | exact superpose b5e51 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e51 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e51 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X0)
               have r₂ := b5e51 X0 X1
               grind)
            | exact resolve b5e17 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e142 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e134 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e134
          have b5e143 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e142 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e142
          have b5e145 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e131
          have b5e149 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e143 X0 X1
               have j1 := b5e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b5e143 X0 X1
               have r₂ := b5e16 (σ X0) (σ X1)
               grind)
            | exact resolve b5e143 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e143
          have b5e151 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e145
               have r₂ := b5e23
               grind)
            | exact resolve b5e145 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e145
          have b5e156 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e149 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e149
            | (have j0 := b5e149 X0 X1
               grind)
            | exact resolve b5e149 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149
          have b5e157 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e151
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e151
            | exact resolve b5e151 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e151
          have b5e158 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e157
               grind)
            | exact superpose b5e157 b5e20
            | exact resolve b5e20 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e159 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e157
               grind)
            | exact superpose b5e157 b5e23
            | exact resolve b5e23 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e167 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e158
               have i₂ := b5e37 x
               grind)
            | exact superpose b5e37 b5e158
            | exact resolve b5e158 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e158
          have b5e755 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e156 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e156
            | exact resolve b5e156 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e798 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e755 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e755
            | (have j0 := b5e755 X0 X1
               grind)
            | exact resolve b5e755 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e755
          have b5e802 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e798 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e798
            | (have j0 := b5e798 X0 X1
               grind)
            | exact resolve b5e798 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e798
          have b5e3539 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e802 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e802
            | exact resolve b5e802 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e802
          have b5e3755 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e3539 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3539
          have b5e3847 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e3755 X0 (M.op X1 X1)
               have i₂ := b5e35 X1 X0
               grind)
            | exact superpose b5e35 b5e3755
            | (have j0 := b5e3755 X0 X1
               grind)
            | exact resolve b5e3755 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e3755
          have b5e4092 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b5e3847 (σ x) (σ y)
               have i₂ := b5e157
               grind)
            | exact superpose b5e157 b5e3847
            | (have j0 := b5e3847 (σ x) (σ y)
               grind)
            | (have r₁ := b5e3847 (σ x) (σ y)
               have r₂ := b5e157
               grind)
            | exact resolve b5e3847 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e157 b5e3847
          have b5e4093 : (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by grind
          clear b5e4092
          have b5e4687 : (k x (τ (M.op (σ y) (σ y)))) = (τ (σ x)) := by
            first
            | (have i₁ := b5e72 x (M.op (σ y) (σ y))
               have i₂ := b5e4093
               grind)
            | exact superpose b5e4093 b5e72
            | exact resolve b5e72 b5e4093
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72 b5e4093
          have b5e4699 : x = (k x (τ (M.op (σ y) (σ y)))) := by
            first
            | (have i₁ := b5e4687
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e4687
            | exact resolve b5e4687 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4687
          have b5e4878 : x = (k x (τ (σ (k y y)))) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e4699
               have i₂ := b5e156 y y
               grind)
            | exact superpose b5e156 b5e4699
            | (have j1 := b5e156 y y
               grind)
            | exact resolve b5e4699 b5e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e156 b5e4699
          have b5e4895 : x = (k x (k y y)) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e4878
               have i₂ := b5e14 (k y y)
               grind)
            | exact superpose b5e14 b5e4878
            | exact resolve b5e4878 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4878
          have b5e7820 : x = (k x (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e4895
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e4895
            | (have j1 := b5e18 y y
               grind)
            | exact resolve b5e4895 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4895
          have b5e7829 : x = (k x (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b5e7820
          have b5e7830 : x = (k x (M.op y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e7829
               have i₂ := b5e37 y
               grind)
            | exact superpose b5e37 b5e7829
            | exact resolve b5e7829 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7829
          have b5e7832 : x = (k x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e7830
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e7830
            | exact resolve b5e7830 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7830
          have b5e7834 : (σ y) = (σ (M.op y x)) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e7832
               have i₂ := b5e37 y
               grind)
            | exact superpose b5e37 b5e7832
            | exact resolve b5e7832 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7832
          have b5e7836 : (σ x) = (σ y) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e7834
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e7834
            | exact resolve b5e7834 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7834
          have b5e7838 : x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b5e7836
               have r₂ := b5e159
               grind)
            | exact resolve b5e7836 b5e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7836
          have b5e7840 : y = (M.op y x) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e7838
               have i₂ := b5e37 y
               grind)
            | exact superpose b5e37 b5e7838
            | exact resolve b5e7838 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e7838
          have b5e7841 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e7840
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e7840
            | exact resolve b5e7840 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7840
          have b5e8083 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e7841
               grind)
            | exact superpose b5e7841 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e7841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7841
          have b5e8095 : x = (M.op x x) ∨ x = y := by grind
          clear b5e8083
          have b5e8420 : (σ x) ≠ (σ x) ∨ x = y := by
            first
            | (have i₁ := b5e167
               have i₂ := b5e8095
               grind)
            | exact superpose b5e8095 b5e167
            | exact resolve b5e167 b5e8095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167 b5e8095
          have b5e8467 : x = y := by grind
          clear b5e8420
          have b5e8777 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e159
               have i₂ := b5e8467
               grind)
            | exact superpose b5e8467 b5e159
            | exact resolve b5e159 b5e8467
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e159 b5e8467
          have b5e8794 : False := by grind
          exact b5e8794
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
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
        have b6e35 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
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
        have b6e37 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op X0 x)
             have i₂ := b6e12 X0 X0 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e35 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e35
          | exact resolve b6e35 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e55 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
        have b6e60 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e55
             have r₂ := b6e21
             grind)
          | exact resolve b6e55 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e64 : x = (M.op x y) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e20
             grind)
          | exact resolve b6e60 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e75 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) X0) = X0 ∨ (M.op X1 X1) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 (M.op X1 X1) X0
             have i₂ := b6e37 X1 X0
             grind)
          | exact superpose b6e37 b6e16
          | (have j0 := b6e16 (M.op X1 X1) X0
             grind)
          | (have r₁ := b6e16 (M.op X1 X1) X1
             have r₂ := b6e37 X1 X1
             grind)
          | exact resolve b6e16 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e78 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b6e75 X0 X1
             have j1 := b6e15 (M.op X1 X1) X0
             grind)
          | (have r₁ := b6e75 X1 X1
             have r₂ := b6e15 (M.op X1 X1) X1
             grind)
          | exact resolve b6e75 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e81 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e64
             grind)
          | exact superpose b6e64 b6e23
          | exact resolve b6e23 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e82 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e64
             grind)
          | exact superpose b6e64 b6e20
          | exact resolve b6e20 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e165 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e54 X0 x
             have i₂ := b6e39 (σ X0)
             grind)
          | exact superpose b6e39 b6e54
          | (have j0 := b6e54 X0 x
             grind)
          | exact resolve b6e54 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e1563 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e39 (σ x)
             have i₂ := b6e165 x
             grind)
          | exact superpose b6e165 b6e39
          | (have j1 := b6e165 x
             grind)
          | exact resolve b6e39 b6e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39 b6e165
        have b6e1587 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by grind
        clear b6e1563
        have b6e1599 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e1587
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1587
          | exact resolve b6e1587 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1587
        have b6e1622 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have r₁ := b6e1599
             have r₂ := b6e81
             grind)
          | exact resolve b6e1599 b6e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81 b6e1599
        have b6e1629 : (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b6e1622
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1622
          | exact resolve b6e1622 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1622
        have b6e1643 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1629
             grind)
          | exact superpose b6e1629 b6e13
          | exact resolve b6e13 b6e1629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1629
        have b6e1684 : y = (k x x) := by
          first
          | (have i₁ := b6e1643
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1643
          | exact resolve b6e1643 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1643
        have b6e1803 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e1684
             grind)
          | exact superpose b6e1684 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e1684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1804 : x = (M.op x x) ∨ y = (M.op x x) := by grind
        clear b6e1803
        have b6e1856 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e78 x x
             have i₂ := b6e1804
             grind)
          | exact superpose b6e1804 b6e78
          | exact resolve b6e78 b6e1804
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78 b6e1804
        have b6e1860 : x = (k x x) ∨ y = (M.op x x) := by grind
        clear b6e1856
        have b6e1863 : x = y ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e1860
             have i₂ := b6e1684
             grind)
          | exact superpose b6e1684 b6e1860
          | exact resolve b6e1860 b6e1684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1684 b6e1860
        have b6e1868 : y = (M.op x x) := by
          first
          | (have r₁ := b6e1863
             have r₂ := b6e82
             grind)
          | exact resolve b6e1863 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82 b6e1863
        have b6e1974 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e37 x X0
             have i₂ := b6e1868
             grind)
          | exact superpose b6e1868 b6e37
          | exact resolve b6e37 b6e1868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e2331 : y = (M.op x y) := by
          first
          | (have i₁ := b6e1868
             have i₂ := b6e1974 x
             grind)
          | exact superpose b6e1974 b6e1868
          | exact resolve b6e1868 b6e1974
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1868 b6e1974
        have b6e2337 : False := by grind
        exact b6e2337
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b7e36 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
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
          have b7e38 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op X0 x)
               have i₂ := b7e13 X0 X0 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e36 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X0 (M.op X1 X1)
               have i₂ := b7e38 X1 X0
               grind)
            | exact superpose b7e38 b7e16
            | (have j0 := b7e16 X0 (M.op X1 X1)
               grind)
            | (have r₁ := b7e16 X1 (M.op X1 X1)
               have r₂ := b7e38 X1 X1
               grind)
            | exact resolve b7e16 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e51 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e48
          have b7e54 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e51
               have r₂ := b7e23
               grind)
            | exact resolve b7e51 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e55 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e54
            | exact resolve b7e54 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e58 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e55
               grind)
            | exact superpose b7e55 b7e14
            | exact resolve b7e14 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : x = (k x y) := by
            first
            | (have i₁ := b7e58
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e58
            | exact resolve b7e58 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e65 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e55
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e55 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e66 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
          have b7e69 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e21
               grind)
            | exact resolve b7e66 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e70 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e22
               grind)
            | exact resolve b7e65 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e73 : y = (M.op y x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e22
               grind)
            | exact resolve b7e69 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e74 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e21
               grind)
            | exact resolve b7e70 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e77 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e59
               grind)
            | exact superpose b7e59 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e78 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e22
               grind)
            | exact resolve b7e77 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e80 : x = (M.op x y) := by
            first
            | (have r₁ := b7e78
               have r₂ := b7e21
               grind)
            | exact resolve b7e78 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e86 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e40 (σ x)
               grind)
            | exact superpose b7e40 b7e20
            | exact resolve b7e20 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e88 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e86
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e86
            | exact resolve b7e86 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e86
          have b7e91 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e22
            | exact resolve b7e22 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e167 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e64 X0 y
               have i₂ := b7e40 (σ X0)
               grind)
            | exact superpose b7e40 b7e64
            | (have j0 := b7e64 X0 y
               grind)
            | exact resolve b7e64 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e197 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X0) (σ X1)
               have i₂ := b7e64 X0 X1
               grind)
            | exact superpose b7e64 b7e17
            | (have j0 := b7e17 (σ X0) (σ X1)
               have j1 := b7e64 X0 X1
               grind)
            | (have r₁ := b7e17 (σ X0) (σ X1)
               have r₂ := b7e64 X0 X1
               grind)
            | (have r₁ := b7e17 (σ X1) (σ X0)
               have r₂ := b7e64 X0 X1
               grind)
            | exact resolve b7e17 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e203 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e64 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e205 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e197 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e197
          have b7e206 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e205 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e205
          have b7e211 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e206 X0 X1
               have j1 := b7e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b7e206 X0 X1
               have r₂ := b7e16 (σ X0) (σ X1)
               grind)
            | exact resolve b7e206 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e206
          have b7e235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e211 X0 X1
               have i₂ := b7e19 X0 X1
               grind)
            | exact superpose b7e19 b7e211
            | (have j0 := b7e211 X0 X1
               grind)
            | exact resolve b7e211 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e211
          have b7e421 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e45 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e443 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b7e421 (M.op X0 X0)
               have i₂ := b7e38 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e38 b7e421
            | exact resolve b7e421 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e421
          have b7e970 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e235 (τ X0) X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e235
            | exact resolve b7e235 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e235
          have b7e1034 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e970 X0 X1
               have i₂ := b7e28 X0 X1
               grind)
            | exact superpose b7e28 b7e970
            | (have j0 := b7e970 X0 X1
               grind)
            | exact resolve b7e970 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e970
          have b7e1045 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e1034 X0 X1
               have i₂ := b7e28 X0 X1
               grind)
            | exact superpose b7e28 b7e1034
            | (have j0 := b7e1034 X0 X1
               grind)
            | exact resolve b7e1034 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e1034
          have b7e1608 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e40 (σ y)
               have i₂ := b7e167 y
               grind)
            | exact superpose b7e167 b7e40
            | (have j1 := b7e167 y
               grind)
            | exact resolve b7e40 b7e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e167
          have b7e1632 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y y)) := by grind
          clear b7e1608
          have b7e1646 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e1632
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1632
            | exact resolve b7e1632 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1632
          have b7e1670 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1646
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1646
            | exact resolve b7e1646 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1646
          have b7e1687 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1670
               grind)
            | exact superpose b7e1670 b7e14
            | exact resolve b7e14 b7e1670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1670
          have b7e1729 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1687
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1687
            | exact resolve b7e1687 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1687
          have b7e4184 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e1045 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1045
            | exact resolve b7e1045 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1045
          have b7e4324 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e4184 y y
               have i₂ := b7e1729
               grind)
            | exact superpose b7e1729 b7e4184
            | exact resolve b7e4184 b7e1729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1729 b7e4184
          have b7e4405 : x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e4324
               have r₂ := b7e91
               grind)
            | exact resolve b7e4324 b7e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91 b7e4324
          have b7e4631 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e443 y
               have i₂ := b7e4405
               grind)
            | exact superpose b7e4405 b7e443
            | exact resolve b7e443 b7e4405
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e443 b7e4405
          have b7e4653 : x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e4631
               have i₂ := b7e80
               grind)
            | exact superpose b7e80 b7e4631
            | exact resolve b7e4631 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e4631
          have b7e4754 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e203 x x
               have i₂ := b7e4653
               grind)
            | exact superpose b7e4653 b7e203
            | (have j0 := b7e203 x x
               grind)
            | exact resolve b7e203 b7e4653
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e203 b7e4653
          have b7e4755 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b7e4754
          have b7e4756 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b7e4755
          have b7e4764 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e4756
               have r₂ := b7e88
               grind)
            | exact resolve b7e4756 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4756
          have b7e4877 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e4764
               grind)
            | exact superpose b7e4764 b7e24
            | exact resolve b7e24 b7e4764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4764
          have b7e4955 : False := by grind
          exact b7e4955
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
          have b8e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e113 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e46 x y
               grind)
            | exact superpose b8e46 b8e24
            | (have j1 := b8e46 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e46 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e46 y x
               grind)
            | exact resolve b8e24 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e127 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e113
          have b8e133 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e127
               have r₂ := b8e23
               grind)
            | exact resolve b8e127 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e139 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e133
               grind)
            | exact superpose b8e133 b8e20
            | exact resolve b8e20 b8e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e139
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e139
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e139 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e286 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e285
          have b8e287 : y = (M.op x y) := by
            first
            | (have r₁ := b8e286
               have r₂ := b8e22
               grind)
            | exact resolve b8e286 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e286
          have b8e288 : False := by grind
          exact b8e288

/-- `Equation3321`: `x ◇ y = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pyx_Equation3321 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3321 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3321.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e35 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 (σ y))) := by
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
      have b0e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
      have b0e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
        intro X0 X1
        grind
      have b0e58 : ∀ X0 X1 X2 : G, (k (M.op X2 X1) X0) = (M.op X0 (M.op X2 X1)) ∨ (M.op X1 X0) = (M.op X1 (M.op X2 X1)) ∨ (M.op X2 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 (M.op X2 X1) X2
           have i₂ := b0e16 (M.op X2 X1) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 (M.op X2 X0))
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X2 X1) X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e129 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e56 (σ X1) (σ X0)
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e56
        | (have j0 := b0e56 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
           grind)
        | exact resolve b0e56 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e511 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e35 (σ y)
           have i₂ := b0e53 X0 y
           grind)
        | exact superpose b0e53 b0e35
        | (have j1 := b0e53 X0 y
           grind)
        | exact resolve b0e35 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e53
      have b0e607 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op x y) = (M.op x X0) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e58 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e58
        | (have j0 := b0e58 (k y X0) y X0
           grind)
        | exact resolve b0e58 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e17749 : (M.op (σ x) (σ x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have j0 := b0e511 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e511
      have b0e17752 : (σ y) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e17749
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e17749
        | exact resolve b0e17749 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e17749
      have b0e17771 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have j1 := b0e129 y x
           grind)
        | (have r₁ := b0e17752
           have r₂ := b0e129 y x
           grind)
        | (have r₁ := b0e17752
           have r₂ := b0e129 y (k y x)
           grind)
        | (have r₁ := b0e17752
           have r₂ := b0e129 (k y x) y
           grind)
        | exact resolve b0e17752 b0e129
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129 b0e17752
      have b0e17776 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e17771
           grind)
        | exact superpose b0e17771 b0e18
        | exact resolve b0e18 b0e17771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e17771
      have b0e18560 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e17776
           have i₂ := b0e607 x
           grind)
        | exact superpose b0e607 b0e17776
        | (have j1 := b0e607 x
           grind)
        | exact resolve b0e17776 b0e607
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e607
      have b0e18564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e17776
           have i₂ := b0e56 x y
           grind)
        | exact superpose b0e56 b0e17776
        | (have j1 := b0e56 x y
           grind)
        | (have r₁ := b0e17776
           have r₂ := b0e56 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e17776
           have r₂ := b0e56 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e17776 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e18568 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e18564
      have b0e18572 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
      clear b0e18560
      have b0e18575 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e18572
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e18572
        | exact resolve b0e18572 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18572
      have b0e19014 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e17776
           have i₂ := b0e18568
           grind)
        | exact superpose b0e18568 b0e17776
        | exact resolve b0e17776 b0e18568
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e17776 b0e18568
      have b0e19029 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e19014
      have b0e21905 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e19029
           have i₂ := b0e18575
           grind)
        | exact superpose b0e18575 b0e19029
        | exact resolve b0e19029 b0e18575
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18575 b0e19029
      have b0e21906 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e21905
      have b0e21907 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e21906
      have b0e22116 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e21907
           grind)
        | exact superpose b0e21907 b0e12
        | exact resolve b0e12 b0e21907
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21907
      have b0e22181 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e22116
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e22116
        | exact resolve b0e22116 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22116
      have b0e22182 : x = y := by grind
      clear b0e22181
      have b0e22736 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e22182
           grind)
        | exact superpose b0e22182 b0e18
        | exact resolve b0e18 b0e22182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22182
      have b0e22837 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e22736
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e22736
        | exact resolve b0e22736 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22736
      have b0e22851 : False := by grind
      exact b0e22851
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : x = y := by
          first
          | (have i₁ := b1e27
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e27
          | exact resolve b1e27 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e29 : x = (k x y) := by grind
        have b1e30 : x = (k x x) := by
          first
          | (have i₁ := b1e29
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e29
          | exact resolve b1e29 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e215 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e55 y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e55
          | (have j0 := b1e55 x
             grind)
          | exact resolve b1e55 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e233 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
          first
          | (have r₁ := b1e215
             have r₂ := b1e25
             grind)
          | exact resolve b1e215 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e215
        have b1e236 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e233
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e233
          | exact resolve b1e233 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e233
        have b1e239 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e236
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e236
          | exact resolve b1e236 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e236
        have b1e241 : False := by grind
        exact b1e241
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
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
        have b2e34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b2e72 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e27 X1 X0
             grind)
          | exact superpose b2e27 b2e13
          | exact resolve b2e13 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e177 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e34 x
             grind)
          | exact superpose b2e34 b2e21
          | (have j1 := b2e34 x
             grind)
          | exact resolve b2e21 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e284 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e72
        have b2e296 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e284 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e284
          | exact resolve b2e284 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e284
        have b2e1265 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e177
        have b2e1266 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1265
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1265
          | exact resolve b2e1265 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1265
        have b2e1267 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1266
        have b2e1268 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e1267
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1267
          | exact resolve b2e1267 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1267
        have b2e3542 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e296 x
             have i₂ := b2e1268
             grind)
          | exact superpose b2e1268 b2e296
          | exact resolve b2e296 b2e1268
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e296 b2e1268
        have b2e3570 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e3542
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e3542
          | exact resolve b2e3542 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3542
        have b2e3624 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by grind
        clear b2e3570
        have b2e3625 : x = (M.op x x) ∨ x = y := by grind
        clear b2e3624
        have b2e3629 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e3625
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3625
          | exact resolve b2e3625 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3625
        have b2e3630 : x = y := by grind
        clear b2e3629
        have b2e3657 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e3630
             grind)
          | exact superpose b2e3630 b2e22
          | exact resolve b2e22 b2e3630
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3630
        have b2e3693 : False := by grind
        exact b2e3693
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e29 : (σ y) = (k (σ y) (σ y)) := by grind
        have b3e30 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e29
          | exact resolve b3e29 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e31 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e32 : y = (k y y) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e52 : y = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e32
        have b3e54 : y = (M.op y y) := by grind
        clear b3e52
        have b3e57 : False := by grind
        exact b3e57
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e163 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e42
          have b4e176 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e163
          have b4e179 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e176
          have b4e180 : y = (M.op y y) := by grind
          clear b4e179
          have b4e181 : False := by grind
          exact b4e181
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : False := by grind
          exact b5e31
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b6e177 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e54 x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e54
          | exact resolve b6e54 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e647 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e177
             grind)
          | exact superpose b6e177 b6e13
          | exact resolve b6e13 b6e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e661 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e647
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e647
          | exact resolve b6e647 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e647
        have b6e909 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e661
        have b6e910 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e909
             have r₂ := b6e20
             grind)
          | exact resolve b6e909 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e909
        have b6e966 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e910
        have b6e1034 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e177
             have i₂ := b6e966
             grind)
          | exact superpose b6e966 b6e177
          | exact resolve b6e177 b6e966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e177 b6e966
        have b6e1037 : (σ x) = (σ y) := by grind
        clear b6e1034
        have b6e1108 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1037
             grind)
          | exact superpose b6e1037 b6e13
          | exact resolve b6e13 b6e1037
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1037
        have b6e1138 : x = y := by
          first
          | (have i₁ := b6e1108
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1108
          | exact resolve b6e1108 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1108
        have b6e1147 : False := by grind
        exact b6e1147
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : x = y := by
            first
            | (have i₁ := b7e29
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e29
            | exact resolve b7e29 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e31 : False := by grind
          exact b7e31
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
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
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
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
          have b8e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e30 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X2 X0) X0 X1
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e27 X0 X1
               grind)
            | exact superpose b8e27 b8e14
            | exact resolve b8e14 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b8e39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            grind
          clear b8e27
          have b8e40 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e39 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e39
            | (have j0 := b8e39 X0
               grind)
            | exact resolve b8e39 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39
          have b8e47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e28 X1 X0
               grind)
            | exact superpose b8e28 b8e14
            | exact resolve b8e14 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e35 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e35
            | exact resolve b8e35 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e118 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          have b8e130 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e118 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e118
            | exact resolve b8e118 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e163 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0
               have i₂ := b8e18 (σ X0) X1
               grind)
            | (have i₁ := b8e38 X0
               have i₂ := b8e18 X0 (M.op (σ X0) (σ X0))
               grind)
            | exact superpose b8e18 b8e38
            | (have j1 := b8e18 (σ X1) X0
               grind)
            | exact resolve b8e38 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e168 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X0) (σ X0) X1
               have i₂ := b8e38 X0
               grind)
            | exact superpose b8e38 b8e30
            | (have j1 := b8e38 X0
               grind)
            | exact resolve b8e30 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e171 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e38 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e172 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e163 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e163
          have b8e394 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X1
               have i₂ := b8e54 X0 X1
               grind)
            | exact superpose b8e54 b8e38
            | (have j1 := b8e54 X0 X1
               grind)
            | exact resolve b8e38 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e408 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b8e394 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e394
          have b8e832 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e171 (τ X0)
               have i₂ := b8e28 X0 (τ X0)
               grind)
            | exact superpose b8e28 b8e171
            | (have j0 := b8e171 (τ X0)
               grind)
            | exact resolve b8e171 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e834 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e832 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e832
            | (have j0 := b8e832 X0
               grind)
            | exact resolve b8e832 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e832
          have b8e837 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e834 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e834
            | (have j0 := b8e834 X0
               grind)
            | exact resolve b8e834 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e834
          have b8e1217 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e40 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e40
            | exact resolve b8e40 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40
          have b8e1248 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e1217 X0
               have i₂ := b8e19 X0 X0
               grind)
            | exact superpose b8e19 b8e1217
            | (have j0 := b8e1217 X0
               grind)
            | exact resolve b8e1217 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1217
          have b8e1691 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e47 X1 X0
               have i₂ := b8e172 X0 X1
               grind)
            | exact superpose b8e172 b8e47
            | (have j1 := b8e172 X0 X1
               grind)
            | exact resolve b8e47 b8e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47 b8e172
          have b8e4111 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e408 x y
               grind)
            | exact superpose b8e408 b8e20
            | (have j1 := b8e408 x y
               grind)
            | exact resolve b8e20 b8e408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e408
          have b8e4277 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) := by
            first
            | (have r₁ := b8e4111
               have r₂ := b8e24
               grind)
            | exact resolve b8e4111 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4111
          have b8e5491 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e168 X0 (σ X0)
               have i₂ := b8e38 X0
               grind)
            | exact superpose b8e38 b8e168
            | (have j0 := b8e168 X0 x
               have j1 := b8e38 X0
               grind)
            | exact resolve b8e168 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e168
          have b8e5560 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e5491 X0
               have j1 := b8e171 X0
               grind)
            | (have r₁ := b8e5491 X0
               have r₂ := b8e171 X0
               grind)
            | exact resolve b8e5491 b8e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5491
          have b8e7208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e4277
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e4277
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e4277
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e4277
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e4277 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4277
          have b8e7210 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b8e7208
          have b8e7214 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b8e7210
               have r₂ := b8e22
               grind)
            | exact resolve b8e7210 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7210
          have b8e7607 : (k y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e14 (k y y)
               have i₂ := b8e7214
               grind)
            | exact superpose b8e7214 b8e14
            | exact resolve b8e14 b8e7214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e7659 : x = (k y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e7607
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e7607
            | exact resolve b8e7607 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7607
          have b8e7901 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b8e7659
          have b8e7919 : y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b8e7901
          have b8e8351 : y = (k y y) ∨ x = (M.op y y) := by grind
          clear b8e7919
          have b8e9040 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e7214
               have i₂ := b8e8351
               grind)
            | exact superpose b8e8351 b8e7214
            | exact resolve b8e7214 b8e8351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7214 b8e8351
          have b8e9065 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
          clear b8e9040
          have b8e9072 : x = (M.op y y) := by
            first
            | (have r₁ := b8e9065
               have r₂ := b8e24
               grind)
            | exact resolve b8e9065 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9065
          have b8e9364 : y = (k y x) := by grind
          have b8e9375 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e30 y x y
               have i₂ := b8e9072
               grind)
            | exact superpose b8e9072 b8e30
            | exact resolve b8e30 b8e9072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e10374 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e9375 y
               have i₂ := b8e9072
               grind)
            | exact superpose b8e9072 b8e9375
            | exact resolve b8e9375 b8e9072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9072 b8e9375
          have b8e78644 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1691 X0 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1691
            | (have j0 := b8e1691 X1 (τ X0)
               grind)
            | exact resolve b8e1691 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1691
          have b8e78708 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e78644 X0 X1
               have i₂ := b8e61 X1 X0
               grind)
            | exact superpose b8e61 b8e78644
            | (have j0 := b8e78644 X0 X1
               grind)
            | exact resolve b8e78644 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e78644
          have b8e78715 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e78708 X0 X1
               have i₂ := b8e28 X0 (τ X0)
               grind)
            | exact superpose b8e28 b8e78708
            | (have j0 := b8e78708 X0 X1
               grind)
            | exact resolve b8e78708 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28 b8e78708
          have b8e78721 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e78715 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e78715
            | (have j0 := b8e78715 X0 X1
               grind)
            | exact resolve b8e78715 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78715
          have b8e93734 : (τ y) = (τ (M.op x y)) ∨ x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b8e78721 y x
               have i₂ := b8e9364
               grind)
            | exact superpose b8e9364 b8e78721
            | (have j0 := b8e78721 y x
               grind)
            | exact resolve b8e78721 b8e9364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9364 b8e78721
          have b8e93826 : (τ y) = (τ (M.op x y)) ∨ x = (k y y) := by
            first
            | (have r₁ := b8e93734
               have r₂ := b8e22
               grind)
            | exact resolve b8e93734 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93734
          have b8e93842 : (τ y) = (τ (M.op x x)) ∨ x = (k y y) := by
            first
            | (have i₁ := b8e93826
               have i₂ := b8e10374
               grind)
            | exact superpose b8e10374 b8e93826
            | exact resolve b8e93826 b8e10374
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93826
          have b8e93881 : (M.op x x) = (σ (τ y)) ∨ x = (k y y) := by
            first
            | (have i₁ := b8e15 (M.op x x)
               have i₂ := b8e93842
               grind)
            | exact superpose b8e93842 b8e15
            | exact resolve b8e15 b8e93842
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93842
          have b8e93960 : y = (M.op x x) ∨ x = (k y y) := by
            first
            | (have i₁ := b8e93881
               have i₂ := b8e15 y
               grind)
            | exact superpose b8e15 b8e93881
            | exact resolve b8e93881 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93881
          have b8e93961 : x = (k y y) := by
            first
            | (have r₁ := b8e93960
               have r₂ := b8e21
               grind)
            | exact resolve b8e93960 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93960
          have b8e102829 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e5560 y
               have i₂ := b8e93961
               grind)
            | exact superpose b8e93961 b8e5560
            | (have j0 := b8e5560 y
               grind)
            | exact resolve b8e5560 b8e93961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5560
          have b8e179860 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear b8e102829
          have b8e179871 : (σ y) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e179860
               have i₂ := b8e19 y y
               grind)
            | exact superpose b8e19 b8e179860
            | exact resolve b8e179860 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179860
          have b8e179873 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e179871
               have i₂ := b8e93961
               grind)
            | exact superpose b8e93961 b8e179871
            | exact resolve b8e179871 b8e93961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93961 b8e179871
          have b8e179875 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b8e179873
               have r₂ := b8e24
               grind)
            | exact resolve b8e179873 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179873
          have b8e179884 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e179875
               grind)
            | exact superpose b8e179875 b8e20
            | exact resolve b8e20 b8e179875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179875
          have b8e180018 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e179884
               have i₂ := b8e10374
               grind)
            | exact superpose b8e10374 b8e179884
            | exact resolve b8e179884 b8e10374
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10374 b8e179884
          have b8e180056 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e180018
               have i₂ := b8e38 x
               grind)
            | exact superpose b8e38 b8e180018
            | (have j1 := b8e38 x
               grind)
            | exact resolve b8e180018 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38
          have b8e188784 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e180056
               have i₂ := b8e1248 x
               grind)
            | exact superpose b8e1248 b8e180056
            | (have j1 := b8e1248 (σ x)
               grind)
            | (have r₁ := b8e180056
               have r₂ := b8e1248 x
               grind)
            | exact resolve b8e180056 b8e1248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1248 b8e180056
          have b8e188786 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b8e188784
          have b8e188803 : x = (k x (τ (σ x))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e130 x
               have i₂ := b8e188786
               grind)
            | exact superpose b8e188786 b8e130
            | exact resolve b8e130 b8e188786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130 b8e188786
          have b8e188929 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e188803
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e188803
            | exact resolve b8e188803 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188803
          have b8e188938 : x = (M.op x x) := by
            first
            | (have j1 := b8e837 x
               grind)
            | (have r₁ := b8e188929
               have r₂ := b8e837 x
               grind)
            | exact resolve b8e188929 b8e837
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e837 b8e188929
          have b8e189101 : x = (k x x) := by grind
          have b8e189391 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e171 x
               have i₂ := b8e189101
               grind)
            | exact superpose b8e189101 b8e171
            | (have j0 := b8e171 x
               grind)
            | exact resolve b8e171 b8e189101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171 b8e189101
          have b8e189498 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b8e189391
          have b8e190296 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e180018
               have i₂ := b8e189498
               grind)
            | exact superpose b8e189498 b8e180018
            | exact resolve b8e180018 b8e189498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180018 b8e189498
          have b8e190517 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e190296
               have i₂ := b8e188938
               grind)
            | exact superpose b8e188938 b8e190296
            | exact resolve b8e190296 b8e188938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188938 b8e190296
          have b8e190518 : False := by grind
          exact b8e190518

/-- `Equation3331`: `x ◇ y = x ◇ (z ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pyx_Equation3331 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3331 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3331.models_iff G M).mp hM
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
      have b0e76 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e80 : False := by grind
      exact b0e80
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
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
          have b4e39 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op y y))) := by
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
          have b4e41 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 X1 (M.op X0 X1)
               have i₂ := b4e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e108 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x (M.op y y)
               have i₂ := b4e39 (M.op y y)
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e114 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e108 X0
               have i₂ := b4e41 y y X0
               grind)
            | exact superpose b4e41 b4e108
            | exact resolve b4e108 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108
          have b4e129 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e41 (σ y) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e41
            | exact resolve b4e41 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e143 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e129 X0
               have i₂ := b4e41 (σ y) (σ y) X0
               grind)
            | exact superpose b4e41 b4e129
            | exact resolve b4e129 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e129
          have b4e161 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e30 x
               have i₂ := b4e143 (σ x)
               grind)
            | exact superpose b4e143 b4e30
            | exact resolve b4e30 b4e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e143
          have b4e162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e161
               have i₂ := b4e114 x
               grind)
            | exact superpose b4e114 b4e161
            | exact resolve b4e161 b4e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114 b4e161
          have b4e166 : False := by grind
          exact b4e166
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
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
          have b5e39 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op y y))) := by
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
          have b5e41 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X1 (M.op X0 X1)
               have i₂ := b5e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) := by
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
          have b5e57 : (M.op y y) ≠ (M.op y y) ∨ x = y ∨ x = (k x y) := by
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
          clear b5e57
          have b5e63 : x = (k x y) := by
            first
            | (have r₁ := b5e62
               have r₂ := b5e21
               grind)
            | exact resolve b5e62 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e74 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
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
          have b5e78 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X0 X0
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e74 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74
          have b5e82 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e71 X0 X1
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e71
            | (have j0 := b5e71 X0 X1
               grind)
            | exact resolve b5e71 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e102 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) y)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x (M.op y y)
               have i₂ := b5e39 (M.op y y)
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e108 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e102 X0
               have i₂ := b5e41 y y X0
               grind)
            | exact superpose b5e41 b5e102
            | exact resolve b5e102 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e102
          have b5e701 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e84 x y
               grind)
            | exact superpose b5e84 b5e20
            | (have j1 := b5e84 x y
               grind)
            | exact resolve b5e20 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e703 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 (σ X1) (σ X0)
               have i₂ := b5e84 X1 X0
               grind)
            | exact superpose b5e84 b5e13
            | (have j1 := b5e84 X1 X0
               grind)
            | exact resolve b5e13 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e756 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e701
               have r₂ := b5e23
               grind)
            | exact resolve b5e701 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e701
          have b5e778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e756
               have i₂ := b5e108 x
               grind)
            | exact superpose b5e108 b5e756
            | exact resolve b5e756 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e756
          have b5e790 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b5e778
               have r₂ := b5e20
               grind)
            | exact resolve b5e778 b5e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e778
          have b5e801 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e790
               have i₂ := b5e82 x y
               grind)
            | exact superpose b5e82 b5e790
            | (have j1 := b5e82 x y
               grind)
            | (have r₁ := b5e790
               have r₂ := b5e82 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b5e790
               have r₂ := b5e82 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b5e790 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82 b5e790
          have b5e804 : y = (k y x) ∨ x = y := by grind
          clear b5e801
          have b5e805 : y = (k y x) := by
            first
            | (have r₁ := b5e804
               have r₂ := b5e21
               grind)
            | exact resolve b5e804 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e804
          have b5e47531 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e703 y x X0
               have i₂ := b5e805
               grind)
            | exact superpose b5e805 b5e703
            | (have j0 := b5e703 y x x
               grind)
            | exact resolve b5e703 b5e805
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e703 b5e805
          have b5e48255 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            intro X0
            first
            | (have j0 := b5e47531 X0
               grind)
            | (have r₁ := b5e47531 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e47531 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47531
          have b5e48314 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b5e48255 X0
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e48255
            | exact resolve b5e48255 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48255
          have b5e48340 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e48314 X0
               have i₂ := b5e108 x
               grind)
            | exact superpose b5e108 b5e48314
            | (have j0 := b5e48314 X0
               grind)
            | exact resolve b5e48314 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108 b5e48314
          have b5e48353 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have j0 := b5e48340 X0
               grind)
            | (have r₁ := b5e48340 X0
               have r₂ := b5e20
               grind)
            | exact resolve b5e48340 b5e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48340
          have b5e48559 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e56 y X0
               have i₂ := b5e48353 (σ y)
               grind)
            | exact superpose b5e48353 b5e56
            | exact resolve b5e56 b5e48353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e49291 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e78 (σ y) (σ x) X0
               have i₂ := b5e48559 (σ y)
               grind)
            | exact superpose b5e48559 b5e78
            | (have j0 := b5e78 (σ y) (σ x) x
               grind)
            | exact resolve b5e78 b5e48559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e49628 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e49291 X0
               grind)
            | (have r₁ := b5e49291 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e49291 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49291
          have b5e49703 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e49628 X0
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e49628
            | exact resolve b5e49628 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e49628
          have b5e49725 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e49703 X0
               have i₂ := b5e48353 X0
               grind)
            | exact superpose b5e48353 b5e49703
            | exact resolve b5e49703 b5e48353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48353 b5e49703
          have b5e49734 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e49725 X0
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e49725
            | (have j0 := b5e49725 X0
               grind)
            | exact resolve b5e49725 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49725
          have b5e49738 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e49734 X0
               have i₂ := b5e63
               grind)
            | exact superpose b5e63 b5e49734
            | (have j0 := b5e49734 X0
               grind)
            | exact resolve b5e49734 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e49734
          have b5e59238 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e49738 (σ y)
               grind)
            | exact superpose b5e49738 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e49738 (σ y)
               grind)
            | exact resolve b5e24 b5e49738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49738
          have b5e59248 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e59238
          have b5e60103 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e48559 X0
               have i₂ := b5e59248
               grind)
            | exact superpose b5e59248 b5e48559
            | exact resolve b5e48559 b5e59248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48559 b5e59248
          have b5e61696 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e60103 (σ y)
               grind)
            | exact superpose b5e60103 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e60103 (σ y)
               grind)
            | exact resolve b5e24 b5e60103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60103
          have b5e61723 : False := by grind
          exact b5e61723
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
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
          have b7e40 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X1 (M.op X0 X1)
               have i₂ := b7e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e61 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = X1 := by
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
          have b7e63 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e59
          have b7e64 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e23
               grind)
            | exact resolve b7e63 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e65 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e64
            | exact resolve b7e64 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e69 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e14
            | exact resolve b7e14 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
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
          have b7e98 : x = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
          have b7e99 : x = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e98
               have r₂ := b7e22
               grind)
            | exact resolve b7e98 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e101 : x = (M.op y x) := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e21
               grind)
            | exact resolve b7e99 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e107 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e40 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e40
            | exact resolve b7e40 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e119 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e107 X0
               have i₂ := b7e40 (σ y) (σ y) X0
               grind)
            | exact superpose b7e40 b7e107
            | exact resolve b7e107 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107
          have b7e125 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b7e40 y x X0
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e40
            | exact resolve b7e40 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e101
          have b7e231 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e30 x
               have i₂ := b7e119 (σ x)
               grind)
            | exact superpose b7e119 b7e30
            | exact resolve b7e30 b7e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e119
          have b7e783 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e231
               grind)
            | exact superpose b7e231 b7e20
            | exact resolve b7e20 b7e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6467 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e61 x (σ y)
               have i₂ := b7e231
               grind)
            | exact superpose b7e231 b7e61
            | (have j0 := b7e61 x (σ y)
               grind)
            | (have r₁ := b7e61 x (σ y)
               have r₂ := b7e231
               grind)
            | exact resolve b7e61 b7e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61 b7e231
          have b7e6510 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
          clear b7e6467
          have b7e6519 : (σ y) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e6510
               have r₂ := b7e23
               grind)
            | exact resolve b7e6510 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6510
          have b7e6534 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e6519
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e6519
            | exact resolve b7e6519 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6519
          have b7e6550 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e6534
               grind)
            | exact superpose b7e6534 b7e14
            | exact resolve b7e14 b7e6534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6534
          have b7e6585 : y = (k y x) := by
            first
            | (have i₁ := b7e6550
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e6550
            | exact resolve b7e6550 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6550
          have b7e7458 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b7e18 y x
               have i₂ := b7e6585
               grind)
            | exact superpose b7e6585 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e6585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6585
          have b7e7459 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e7458
               have r₂ := b7e21
               grind)
            | exact resolve b7e7458 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7458
          have b7e9517 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e783
               have i₂ := b7e7459
               grind)
            | exact superpose b7e7459 b7e783
            | exact resolve b7e783 b7e7459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e783 b7e7459
          have b7e9557 : y = (M.op x y) := by grind
          clear b7e9517
          have b7e9752 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e125 X0
               have i₂ := b7e9557
               grind)
            | exact superpose b7e9557 b7e125
            | exact resolve b7e125 b7e9557
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125 b7e9557
          have b7e9940 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e9752 y
               grind)
            | exact superpose b7e9752 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e9752 y
               grind)
            | exact resolve b7e22 b7e9752
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9752
          have b7e9941 : False := by grind
          exact b7e9941
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
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
          have b8e40 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 X1 (M.op X0 X1)
               have i₂ := b8e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e58 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = X1 := by
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
          have b8e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
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
          have b8e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e89 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e79 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e79
            | (have j0 := b8e79 X0 X1
               grind)
            | exact resolve b8e79 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e109 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e40 X0 X0 X2
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e40 X1 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e40
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e40 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e110 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e40 (σ X0) (σ X0) X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e40
            | exact resolve b8e40 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e121 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e109 X0 X1 X2
               have i₂ := b8e40 X0 X1 X2
               grind)
            | exact superpose b8e40 b8e109
            | (have j0 := b8e109 X0 X1 X2
               grind)
            | exact resolve b8e109 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e633 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e91 x y
               grind)
            | exact superpose b8e91 b8e20
            | (have j1 := b8e91 x y
               grind)
            | exact resolve b8e20 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e663 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op X1 (σ X2)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (σ X0) = (σ X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e40 (σ X0) (σ X2) X1
               have i₂ := b8e91 X0 X2
               grind)
            | exact superpose b8e91 b8e40
            | (have j1 := b8e91 X0 X2
               grind)
            | exact resolve b8e40 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e91
          have b8e688 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (σ X0) = (σ X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e663 X0 X1 X2
               have i₂ := b8e110 X0 X1
               grind)
            | exact superpose b8e110 b8e663
            | (have j0 := b8e663 X0 X1 X2
               grind)
            | exact resolve b8e663 b8e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110 b8e663
          have b8e699 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e633
               have r₂ := b8e23
               grind)
            | exact resolve b8e633 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e633
          have b8e5374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e699
               have i₂ := b8e89 x y
               grind)
            | exact superpose b8e89 b8e699
            | (have j1 := b8e89 x y
               grind)
            | (have r₁ := b8e699
               have r₂ := b8e89 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e699
               have r₂ := b8e89 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e699 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89 b8e699
          have b8e5377 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (k y x) ∨ x = y := by grind
          clear b8e5374
          have b8e5382 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b8e5377
               have r₂ := b8e21
               grind)
            | exact resolve b8e5377 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5377
          have b8e5392 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e58 x (σ y)
               have i₂ := b8e5382
               grind)
            | exact superpose b8e5382 b8e58
            | (have j0 := b8e58 x (σ y)
               grind)
            | (have r₁ := b8e58 x (σ y)
               have r₂ := b8e5382
               grind)
            | exact resolve b8e58 b8e5382
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58 b8e5382
          have b8e5426 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
          clear b8e5392
          have b8e5439 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b8e5426
               have r₂ := b8e23
               grind)
            | exact resolve b8e5426 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5426
          have b8e5444 : (σ y) = (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e5439
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e5439
            | exact resolve b8e5439 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5439
          have b8e5463 : (k y x) = (τ (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e5444
               grind)
            | exact superpose b8e5444 b8e14
            | exact resolve b8e14 b8e5444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5444
          have b8e5507 : y = (k y x) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e5463
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e5463
            | exact resolve b8e5463 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5463
          have b8e5508 : y = (k y x) := by grind
          clear b8e5507
          have b8e5598 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e121 x y X0
               have i₂ := b8e5508
               grind)
            | exact superpose b8e5508 b8e121
            | (have j0 := b8e121 y x X0
               grind)
            | exact resolve b8e121 b8e5508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121
          have b8e5605 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e5598 X0
               grind)
            | (have r₁ := b8e5598 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e5598 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5598
          have b8e9110 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e688 x X0 y
               grind)
            | exact superpose b8e688 b8e20
            | (have j1 := b8e688 y X0 x
               grind)
            | exact resolve b8e20 b8e688
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e688
          have b8e9441 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b8e9110 X0
               grind)
            | (have r₁ := b8e9110 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e9110 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9110
          have b8e9471 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e9441 X0
               have i₂ := b8e5508
               grind)
            | exact superpose b8e5508 b8e9441
            | (have j0 := b8e9441 X0
               grind)
            | exact resolve b8e9441 b8e5508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5508 b8e9441
          have b8e9476 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 x) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b8e9471 X0
               have i₂ := b8e5605 X1
               grind)
            | exact superpose b8e5605 b8e9471
            | (have j0 := b8e9471 X0
               have j1 := b8e5605 X1
               grind)
            | exact resolve b8e9471 b8e5605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5605 b8e9471
          have b8e9477 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 x) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have j0 := b8e9476 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9476
          have b8e16980 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e9477 (σ y) X0
               grind)
            | exact superpose b8e9477 b8e24
            | (have j1 := b8e9477 X0 X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e9477 (σ y) x
               grind)
            | exact resolve b8e24 b8e9477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9477
          have b8e17069 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e16980 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16980
          have b8e17548 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e17069 y
               grind)
            | exact superpose b8e17069 b8e22
            | (have r₁ := b8e22
               have r₂ := b8e17069 y
               grind)
            | exact resolve b8e22 b8e17069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17069
          have b8e17550 : False := by grind
          exact b8e17550

/-- `Equation3398`: `x ◇ y = z ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pyx_Equation3398 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3398 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3398.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (y) (x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          grind
        have b0e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          grind
        clear b0e31
        have b0e74 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
        clear b0e32
        have b0e78 : False := by grind
        exact b0e78
      · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
        · have b1e21 : x = y := by grind
          have b1e23 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e31 : False := by grind
          exact b1e31
        · have b2e21 : x = y := by grind
          have b2e23 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e31 : False := by grind
          exact b2e31
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b3e21 : x = y := by grind
          have b3e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e31 : False := by grind
          exact b3e31
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b4e22 : x = y := by grind
            have b4e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e34 : False := by grind
            exact b4e34
          · have b5e22 : x = y := by grind
            have b5e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e34 : False := by grind
            exact b5e34
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b6e21 : x = y := by grind
          have b6e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e31 : False := by grind
          exact b6e31
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b7e22 : x = y := by grind
            have b7e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e34 : False := by grind
            exact b7e34
          · have b8e22 : x = y := by grind
            have b8e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e34 : False := by grind
            exact b8e34
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b9e21 : x ≠ y := by grind
          have b9e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e31 : False := by grind
          exact b9e31
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
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
            have b11e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 y
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e15
              | exact resolve b11e15 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e31 : x = y := by
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
            have b11e32 : False := by grind
            exact b11e32
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b12e24 : (σ x) ≠ (σ y) := by grind
            have b12e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e34 : False := by grind
            exact b12e34
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
                intro X0 X1 X2
                grind
              have b13e24 : x = (M.op y y) := by grind
              have b13e27 : x ≠ y := by grind
              have b13e28 : y = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e46 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) := by
                intro X0
                first
                | (have i₁ := b13e15 x X0 x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e47 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 x)) := by
                intro X0
                first
                | (have i₁ := b13e15 y X0 y
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e50 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op x X0)) := by
                intro X0
                first
                | (have i₁ := b13e15 X0 x y
                   have i₂ := b13e46 X0
                   grind)
                | exact superpose b13e46 b13e15
                | exact resolve b13e15 b13e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e46
              have b13e77 : (M.op y y) = (M.op y x) := by
                first
                | (have i₁ := b13e47 x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e47
                | exact resolve b13e47 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e80 : x = (M.op y x) := by
                first
                | (have i₁ := b13e77
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e77
                | exact resolve b13e77 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e77
              have b13e118 : (M.op x x) = (M.op y x) := by
                first
                | (have i₁ := b13e47 x
                   have i₂ := b13e50 x
                   grind)
                | exact superpose b13e50 b13e47
                | exact resolve b13e47 b13e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e47 b13e50
              have b13e123 : x = (M.op x x) := by
                first
                | (have i₁ := b13e118
                   have i₂ := b13e80
                   grind)
                | exact superpose b13e80 b13e118
                | exact resolve b13e118 b13e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e80 b13e118
              have b13e127 : x = y := by
                first
                | (have i₁ := b13e123
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e123
                | exact resolve b13e123 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e123
              have b13e129 : False := by grind
              exact b13e129
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
                intro X0 X1 X2
                grind
              have b14e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : x = (M.op y y) := by grind
              have b14e25 : (σ x) ≠ (σ y) := by grind
              have b14e27 : x ≠ y := by grind
              have b14e28 : y ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b14e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b14e34
              have b14e44 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 x)) := by
                intro X0
                first
                | (have i₁ := b14e15 y X0 y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e48 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op y X0)) := by
                intro X0
                first
                | (have i₁ := b14e15 X0 y x
                   have i₂ := b14e44 X0
                   grind)
                | exact superpose b14e44 b14e15
                | exact resolve b14e15 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
              have b14e68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e59 X0 X1
                   have i₂ := b14e35 X0
                   grind)
                | exact superpose b14e35 b14e59
                | (have j0 := b14e59 X0 X1
                   grind)
                | exact resolve b14e59 b14e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e35 b14e59
              have b14e74 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op X0 y)) := by
                intro X0
                first
                | (have i₁ := b14e15 y x X0
                   have i₂ := b14e48 X0
                   grind)
                | exact superpose b14e48 b14e15
                | exact resolve b14e15 b14e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e48
              have b14e105 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b14e15 X0 X0 y
                   have i₂ := b14e74 X0
                   grind)
                | exact superpose b14e74 b14e15
                | exact resolve b14e15 b14e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e74
              have b14e109 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
                intro X0
                first
                | (have i₁ := b14e105 X0
                   have i₂ := b14e44 y
                   grind)
                | exact superpose b14e44 b14e105
                | exact resolve b14e105 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44 b14e105
              have b14e110 : ∀ X0 : G, (M.op X0 X0) = x := by
                intro X0
                first
                | (have i₁ := b14e109 X0
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e109
                | exact resolve b14e109 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e109
              have b14e535 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e68 x y
                   grind)
                | exact superpose b14e68 b14e22
                | (have j1 := b14e68 x y
                   grind)
                | exact resolve b14e22 b14e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e68
              have b14e573 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
                first
                | (have r₁ := b14e535
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e535 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e535
              have b14e616 : (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
                first
                | (have i₁ := b14e573
                   have i₂ := b14e110 x
                   grind)
                | exact superpose b14e110 b14e573
                | exact resolve b14e573 b14e110
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e110 b14e573
              have b14e645 : (σ (M.op x y)) ≠ (σ (k y x)) := by
                first
                | (have r₁ := b14e616
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e616 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e616
              have b14e760 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b14e645
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e645
                | (have j1 := b14e20 y x
                   grind)
                | (have r₁ := b14e645
                   have r₂ := b14e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b14e645
                   have r₂ := b14e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b14e645 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e645
              have b14e762 : y = (M.op x x) ∨ x = y := by grind
              clear b14e760
              have b14e767 : x = y := by
                first
                | (have r₁ := b14e762
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e762 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e762
              have b14e770 : False := by grind
              exact b14e770
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b15e24 : (σ x) ≠ (σ y) := by grind
            have b15e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e34 : False := by grind
            exact b15e34
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b16e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e24 : x = (M.op y y) := by grind
              have b16e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b16e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b16e34
              have b16e101 : (σ x) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b16e26
                   have i₂ := b16e35 y
                   grind)
                | exact superpose b16e35 b16e26
                | exact resolve b16e26 b16e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e35
              have b16e106 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b16e101
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e101
                | exact resolve b16e101 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e101
              have b16e107 : False := by grind
              exact b16e107
            · have b17e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e24 : x = (M.op y y) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b17e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b17e34
              have b17e94 : (σ x) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e35 y
                   grind)
                | exact superpose b17e35 b17e26
                | exact resolve b17e26 b17e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35
              have b17e99 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b17e94
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e94
                | exact resolve b17e94 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e94
              have b17e100 : False := by grind
              exact b17e100
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b18e21 : x ≠ y := by grind
          have b18e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e31 : False := by grind
          exact b18e31
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
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
            have b20e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 y
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e15
              | exact resolve b20e15 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e31 : x = y := by
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
            have b20e32 : False := by grind
            exact b20e32
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b21e24 : (σ x) ≠ (σ y) := by grind
            have b21e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e34 : False := by grind
            exact b21e34
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e24 : x ≠ (M.op y y) := by grind
              have b22e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b22e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b22e34
              have b22e106 : (σ x) = (σ (M.op y y)) := by
                first
                | (have i₁ := b22e26
                   have i₂ := b22e35 y
                   grind)
                | exact superpose b22e35 b22e26
                | exact resolve b22e26 b22e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e35
              have b22e161 : (M.op y y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (M.op y y)
                   have i₂ := b22e106
                   grind)
                | exact superpose b22e106 b22e16
                | exact resolve b22e16 b22e106
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e106
              have b22e162 : x = (M.op y y) := by
                first
                | (have i₁ := b22e161
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e161
                | exact resolve b22e161 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e161
              have b22e166 : False := by grind
              exact b22e166
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e24 : x ≠ (M.op y y) := by grind
              have b23e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b23e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b23e34
              have b23e99 : (σ x) = (σ (M.op y y)) := by
                first
                | (have i₁ := b23e26
                   have i₂ := b23e35 y
                   grind)
                | exact superpose b23e35 b23e26
                | exact resolve b23e26 b23e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e35
              have b23e145 : (M.op y y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (M.op y y)
                   have i₂ := b23e99
                   grind)
                | exact superpose b23e99 b23e16
                | exact resolve b23e16 b23e99
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e99
              have b23e146 : x = (M.op y y) := by
                first
                | (have i₁ := b23e145
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e145
                | exact resolve b23e145 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e145
              have b23e150 : False := by grind
              exact b23e150
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b24e24 : (σ x) ≠ (σ y) := by grind
            have b24e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e34 : False := by grind
            exact b24e34
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
                intro X0 X1 X2
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e24 : x ≠ (M.op y y) := by grind
              have b25e25 : (σ x) ≠ (σ y) := by grind
              have b25e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              have b25e27 : x ≠ y := by grind
              have b25e28 : y = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 (τ X0) X1
                   have i₂ := b25e17 X0
                   grind)
                | exact superpose b25e17 b25e21
                | exact resolve b25e21 b25e17
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
              have b25e44 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) := by
                intro X0
                first
                | (have i₁ := b25e15 x X0 x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e45 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X1 (M.op X0 X2)) (M.op X3 (M.op X0 X1))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X2 X3 (M.op X1 (M.op X0 X2))
                   have i₂ := b25e15 X0 X1 X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e46 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X2) (M.op X0 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X1 X2 (M.op X0 X2)
                   have i₂ := b25e15 X0 X1 X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e47 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op x X0)) := by
                intro X0
                first
                | (have i₁ := b25e15 X0 x y
                   have i₂ := b25e44 X0
                   grind)
                | exact superpose b25e44 b25e15
                | exact resolve b25e15 b25e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
              have b25e57 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b25e60 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
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
                | (have r₁ := b25e26
                   have r₂ := b25e20 (σ x) (M.op (σ y) (σ y))
                   grind)
                | (have r₁ := b25e26
                   have r₂ := b25e20 (M.op (σ y) (σ y)) (σ x)
                   grind)
                | exact resolve b25e26 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e61 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e20 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e57 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e57
              have b25e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e54 X0 X1
                   have i₂ := b25e35 X0
                   grind)
                | exact superpose b25e35 b25e54
                | (have j0 := b25e54 X0 X1
                   grind)
                | exact resolve b25e54 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e54
              have b25e65 : y = (M.op y y) := by
                first
                | (have i₁ := b25e47 x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e47
                | exact resolve b25e47 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e69 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) := by
                intro X0
                first
                | (have i₁ := b25e15 x y X0
                   have i₂ := b25e47 X0
                   grind)
                | exact superpose b25e47 b25e15
                | exact resolve b25e15 b25e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e47
              have b25e100 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x y)) := by
                intro X0
                first
                | (have i₁ := b25e15 X0 X0 x
                   have i₂ := b25e69 X0
                   grind)
                | exact superpose b25e69 b25e15
                | exact resolve b25e15 b25e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e104 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
                intro X0
                first
                | (have i₁ := b25e100 X0
                   have i₂ := b25e44 x
                   grind)
                | exact superpose b25e44 b25e100
                | exact resolve b25e100 b25e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44 b25e100
              have b25e105 : ∀ X0 : G, (M.op X0 X0) = y := by
                intro X0
                first
                | (have i₁ := b25e104 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e104
                | exact resolve b25e104 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e104
              have b25e130 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X2 X0) (M.op X3 (M.op X0 X1))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 (M.op X2 X1) X3 (M.op X2 X0)
                   have i₂ := b25e46 X2 X0 X1
                   grind)
                | exact superpose b25e46 b25e15
                | exact resolve b25e15 b25e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e147 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 (M.op X0 X1) X1
                   have i₂ := b25e105 (M.op X0 X1)
                   grind)
                | exact superpose b25e105 b25e15
                | exact resolve b25e15 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e149 : y ≠ (σ x) := by
                first
                | (have i₁ := b25e26
                   have i₂ := b25e105 (σ y)
                   grind)
                | exact superpose b25e105 b25e26
                | exact resolve b25e26 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e150 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e35 X0
                   have i₂ := b25e105 (σ X0)
                   grind)
                | exact superpose b25e105 b25e35
                | exact resolve b25e35 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35
              have b25e153 : y = (σ y) := by
                first
                | (have i₁ := b25e150 x
                   have i₂ := b25e105 x
                   grind)
                | exact superpose b25e105 b25e150
                | exact resolve b25e150 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e150
              have b25e189 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X0 (M.op X3 X2)) (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e45 X3 X0 X2 (M.op X3 X1)
                   have i₂ := b25e46 X3 X0 X1
                   grind)
                | exact superpose b25e46 b25e45
                | exact resolve b25e45 b25e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e210 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X1 (M.op X3 X2)) := by
                intro X1 X2 X3
                first
                | (have i₁ := b25e189 x X1 X2 X3
                   have i₂ := b25e46 x X1 (M.op X3 X2)
                   grind)
                | exact superpose b25e46 b25e189
                | exact resolve b25e189 b25e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e46 b25e189
              have b25e271 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ y = X0 := by
                intro X0
                first
                | (have i₁ := b25e61 X0 y
                   have i₂ := b25e65
                   grind)
                | exact superpose b25e65 b25e61
                | (have j0 := b25e61 X0 y
                   grind)
                | (have r₁ := b25e61 X0 y
                   have r₂ := b25e65
                   grind)
                | exact resolve b25e61 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e61 b25e65
              have b25e272 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = X0 := by
                intro X0
                first
                | (have j0 := b25e271 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e271
              have b25e277 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e153
                   grind)
                | exact superpose b25e153 b25e22
                | exact resolve b25e22 b25e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e280 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) := by
                intro X0
                first
                | (have i₁ := b25e21 X0 y
                   have i₂ := b25e153
                   grind)
                | exact superpose b25e153 b25e21
                | exact resolve b25e21 b25e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e282 : y = (τ y) := by
                first
                | (have i₁ := b25e16 y
                   have i₂ := b25e153
                   grind)
                | exact superpose b25e153 b25e16
                | exact resolve b25e16 b25e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e291 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e62 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e62
              have b25e298 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
                first
                | (have j0 := b25e60 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e60
              have b25e299 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b25e298
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e298 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e298
              have b25e300 : (k (σ x) y) = (M.op y (σ x)) := by
                first
                | (have i₁ := b25e299
                   have i₂ := b25e153
                   grind)
                | exact superpose b25e153 b25e299
                | exact resolve b25e299 b25e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e299
              have b25e301 : (M.op y (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b25e300
                   have i₂ := b25e280 x
                   grind)
                | exact superpose b25e280 b25e300
                | exact resolve b25e300 b25e280
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e300
              have b25e387 : ∀ X0 : G, (σ (k X0 y)) = (M.op y (σ X0)) ∨ (σ X0) = (σ (M.op y y)) ∨ (σ X0) = y := by
                intro X0
                first
                | (have i₁ := b25e63 y x
                   have i₂ := b25e153
                   grind)
                | exact superpose b25e153 b25e63
                | (have j0 := b25e63 y X0
                   grind)
                | exact resolve b25e63 b25e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e410 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (M.op X3 (σ (k X0 X1))) (M.op X2 (M.op (σ X1) X3))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e45 (σ X1) X3 (σ X0) X2
                   have i₂ := b25e63 X1 X0
                   grind)
                | exact superpose b25e63 b25e45
                | (have j1 := b25e63 X1 X0
                   grind)
                | exact resolve b25e45 b25e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e45 b25e63
              have b25e441 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (M.op (σ X1) X3) (M.op X2 (M.op X3 (σ (k X0 X1))))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e410 X0 X1 X2 X3
                   have i₂ := b25e210 (M.op (σ X1) X3) (M.op X3 (σ (k X0 X1))) X2
                   grind)
                | (have i₁ := b25e410 X0 X1 X2 X3
                   have i₂ := b25e210 (M.op X3 (σ (k X0 X1))) (M.op (σ X1) X3) X2
                   grind)
                | exact superpose b25e210 b25e410
                | (have j0 := b25e410 X0 X1 X2 X3
                   grind)
                | exact resolve b25e410 b25e210
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e210 b25e410
              have b25e461 : ∀ X0 : G, (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op y (σ X0)) ∨ (σ X0) = y := by
                intro X0
                first
                | (have i₁ := b25e387 X0
                   have i₂ := b25e105 y
                   grind)
                | exact superpose b25e105 b25e387
                | (have j0 := b25e387 X0
                   grind)
                | exact resolve b25e387 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e387
              have b25e482 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (M.op (σ X1) (σ (k X0 X1))) X2) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e441 X0 X1 X2 x
                   have i₂ := b25e130 x (σ (k X0 X1)) (σ X1) X2
                   grind)
                | exact superpose b25e130 b25e441
                | (have j0 := b25e441 X0 X1 X2 x
                   grind)
                | exact resolve b25e441 b25e130
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e130 b25e441
              have b25e498 : ∀ X0 : G, (σ X0) = y ∨ (σ (k X0 y)) = (M.op y (σ X0)) ∨ (σ X0) = y := by
                intro X0
                first
                | (have i₁ := b25e461 X0
                   have i₂ := b25e153
                   grind)
                | exact superpose b25e153 b25e461
                | (have j0 := b25e461 X0
                   grind)
                | exact resolve b25e461 b25e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e461
              have b25e499 : ∀ X0 : G, (σ (k X0 y)) = (M.op y (σ X0)) ∨ (σ X0) = y := by
                intro X0
                first
                | (have j0 := b25e498 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e498
              have b25e509 : ∀ X0 X1 X2 : G, (σ X0) = (σ y) ∨ (M.op (σ X0) X2) = (M.op (M.op (σ X1) (σ (k X0 X1))) X2) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e482 X0 X1 X2
                   have i₂ := b25e105 X1
                   grind)
                | exact superpose b25e105 b25e482
                | (have j0 := b25e482 X0 X1 X2
                   grind)
                | exact resolve b25e482 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e482
              have b25e521 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (M.op (σ X1) (σ (k X0 X1))) X2) ∨ (σ X0) = y ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e509 X0 X1 X2
                   have i₂ := b25e153
                   grind)
                | exact superpose b25e153 b25e509
                | (have j0 := b25e509 X0 X1 X2
                   grind)
                | exact resolve b25e509 b25e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e509
              have b25e957 : (M.op y (σ x)) = (σ (M.op y x)) ∨ x = (M.op y y) ∨ x = y := by
                first
                | (have i₁ := b25e301
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e301
                | (have j1 := b25e20 x y
                   grind)
                | exact resolve b25e301 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e301
              have b25e971 : (M.op y (σ x)) = (σ (M.op y x)) ∨ x = y := by
                first
                | (have r₁ := b25e957
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e957 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e957
              have b25e978 : (M.op y (σ x)) = (σ (M.op y x)) := by
                first
                | (have r₁ := b25e971
                   have r₂ := b25e27
                   grind)
                | exact resolve b25e971 b25e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e971
              have b25e1741 : (M.op y x) = (τ (M.op y (σ x))) := by
                first
                | (have i₁ := b25e16 (M.op y x)
                   have i₂ := b25e978
                   grind)
                | exact superpose b25e978 b25e16
                | exact resolve b25e16 b25e978
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e3793 : (σ (k (M.op y x) y)) = (k (M.op y (σ x)) y) := by
                first
                | (have i₁ := b25e280 (M.op y x)
                   have i₂ := b25e978
                   grind)
                | exact superpose b25e978 b25e280
                | exact resolve b25e280 b25e978
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e280
              have b25e9171 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) ∨ (τ X0) = y := by
                intro X0
                first
                | (have i₁ := b25e31 X0 y
                   have i₂ := b25e272 (τ X0)
                   grind)
                | exact superpose b25e272 b25e31
                | (have j1 := b25e272 (τ X0)
                   grind)
                | exact resolve b25e31 b25e272
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e31 b25e272
              have b25e9175 : ∀ X0 : G, (k X0 y) = (σ (M.op y (τ X0))) ∨ (τ X0) = y := by
                intro X0
                first
                | (have i₁ := b25e9171 X0
                   have i₂ := b25e153
                   grind)
                | exact superpose b25e153 b25e9171
                | (have j0 := b25e9171 X0
                   grind)
                | exact resolve b25e9171 b25e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9171
              have b25e53047 : (k (M.op y (σ x)) y) = (σ (M.op y (M.op y x))) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e9175 (M.op y (σ x))
                   have i₂ := b25e1741
                   grind)
                | exact superpose b25e1741 b25e9175
                | exact resolve b25e9175 b25e1741
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9175
              have b25e53118 : (σ (M.op x y)) = (k (M.op y (σ x)) y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e53047
                   have i₂ := b25e69 y
                   grind)
                | exact superpose b25e69 b25e53047
                | exact resolve b25e53047 b25e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e69 b25e53047
              have b25e53127 : (σ (M.op x y)) = (σ (k (M.op y x) y)) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e53118
                   have i₂ := b25e3793
                   grind)
                | exact superpose b25e3793 b25e53118
                | exact resolve b25e53118 b25e3793
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3793 b25e53118
              have b25e396789 : (σ (M.op x y)) = (M.op y (σ (M.op y x))) ∨ y = (σ (M.op y x)) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e499 (M.op y x)
                   have i₂ := b25e53127
                   grind)
                | exact superpose b25e53127 b25e499
                | (have j0 := b25e499 (M.op y x)
                   grind)
                | exact resolve b25e499 b25e53127
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e499 b25e53127
              have b25e396811 : (σ (M.op x y)) = (M.op y (M.op y (σ x))) ∨ y = (σ (M.op y x)) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e396789
                   have i₂ := b25e978
                   grind)
                | exact superpose b25e978 b25e396789
                | exact resolve b25e396789 b25e978
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e396789
              have b25e396814 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ (M.op y x)) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e396811
                   have i₂ := b25e147 y (σ x)
                   grind)
                | exact superpose b25e147 b25e396811
                | exact resolve b25e396811 b25e147
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e396811
              have b25e396817 : y = (σ (M.op y x)) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b25e396814
                   have r₂ := b25e277
                   grind)
                | exact resolve b25e396814 b25e277
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e396814
              have b25e396819 : y = (M.op y (σ x)) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e396817
                   have i₂ := b25e978
                   grind)
                | exact superpose b25e978 b25e396817
                | exact resolve b25e396817 b25e978
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e978 b25e396817
              have b25e396878 : (M.op y x) = (τ y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e1741
                   have i₂ := b25e396819
                   grind)
                | exact superpose b25e396819 b25e1741
                | exact resolve b25e1741 b25e396819
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1741 b25e396819
              have b25e397156 : y = (M.op y x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e396878
                   have i₂ := b25e282
                   grind)
                | exact superpose b25e282 b25e396878
                | exact resolve b25e396878 b25e282
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e282 b25e396878
              have b25e397157 : y = (M.op y x) := by grind
              clear b25e397156
              have b25e397394 : (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b25e147 y x
                   have i₂ := b25e397157
                   grind)
                | exact superpose b25e397157 b25e147
                | exact resolve b25e147 b25e397157
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e147
              have b25e397415 : y ≠ y ∨ x = y ∨ y = (k x y) := by
                first
                | (have i₁ := b25e291 x y
                   have i₂ := b25e397157
                   grind)
                | exact superpose b25e397157 b25e291
                | (have j0 := b25e291 x y
                   grind)
                | (have r₁ := b25e291 x y
                   have r₂ := b25e397157
                   grind)
                | exact resolve b25e291 b25e397157
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e291 b25e397157
              have b25e397603 : x = y ∨ y = (k x y) := by grind
              clear b25e397415
              have b25e397762 : y = (k x y) := by
                first
                | (have r₁ := b25e397603
                   have r₂ := b25e27
                   grind)
                | exact resolve b25e397603 b25e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e397603
              have b25e397778 : y = (M.op x y) := by
                first
                | (have i₁ := b25e397394
                   have i₂ := b25e105 y
                   grind)
                | exact superpose b25e105 b25e397394
                | exact resolve b25e397394 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e397394
              have b25e398333 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (σ y)) X0) ∨ y = (σ x) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have i₁ := b25e521 x y X0
                   have i₂ := b25e397762
                   grind)
                | exact superpose b25e397762 b25e521
                | (have j0 := b25e521 x y x
                   grind)
                | exact resolve b25e521 b25e397762
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e521 b25e397762
              have b25e398355 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have j0 := b25e398333 X0
                   grind)
                | (have r₁ := b25e398333 X0
                   have r₂ := b25e149
                   grind)
                | exact resolve b25e398333 b25e149
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e149 b25e398333
              have b25e398397 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
                intro X0
                first
                | (have j0 := b25e398355 X0
                   grind)
                | (have r₁ := b25e398355 X0
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e398355 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e398355
              have b25e398435 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b25e398397 X0
                   have i₂ := b25e105 (σ y)
                   grind)
                | exact superpose b25e105 b25e398397
                | exact resolve b25e398397 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e398397
              have b25e398542 : (σ y) ≠ (M.op (σ x) y) := by
                first
                | (have i₁ := b25e277
                   have i₂ := b25e397778
                   grind)
                | exact superpose b25e397778 b25e277
                | exact resolve b25e277 b25e397778
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e277 b25e397778
              have b25e399020 : (σ y) ≠ (M.op y y) := by
                first
                | (have i₁ := b25e398542
                   have i₂ := b25e398435 y
                   grind)
                | exact superpose b25e398435 b25e398542
                | exact resolve b25e398542 b25e398435
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e398435 b25e398542
              have b25e399194 : y ≠ (σ y) := by
                first
                | (have i₁ := b25e399020
                   have i₂ := b25e105 y
                   grind)
                | exact superpose b25e105 b25e399020
                | exact resolve b25e399020 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e105 b25e399020
              have b25e399290 : False := by grind
              exact b25e399290
            · have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e25 : (σ x) ≠ (σ y) := by grind
              have b26e27 : x ≠ y := by grind
              have b26e28 : y ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b26e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b26e34
              have b26e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
              have b26e80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e71 X0 X1
                   have i₂ := b26e35 X0
                   grind)
                | exact superpose b26e35 b26e71
                | (have j0 := b26e71 X0 X1
                   grind)
                | exact resolve b26e71 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e71
              have b26e320 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e80 x y
                   grind)
                | exact superpose b26e80 b26e22
                | (have j1 := b26e80 x y
                   grind)
                | exact resolve b26e22 b26e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e80
              have b26e365 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
                first
                | (have r₁ := b26e320
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e320 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e320
              have b26e6254 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b26e365
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e365
                | (have j1 := b26e20 y x
                   grind)
                | (have r₁ := b26e365
                   have r₂ := b26e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b26e365
                   have r₂ := b26e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b26e365 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e365
              have b26e6256 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by grind
              clear b26e6254
              have b26e6260 : (σ y) = (σ (M.op x x)) ∨ x = y := by
                first
                | (have r₁ := b26e6256
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e6256 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6256
              have b26e6264 : (σ y) = (σ (M.op x x)) := by
                first
                | (have r₁ := b26e6260
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e6260 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6260
              have b26e6284 : (M.op x x) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (M.op x x)
                   have i₂ := b26e6264
                   grind)
                | exact superpose b26e6264 b26e16
                | exact resolve b26e16 b26e6264
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6264
              have b26e6317 : y = (M.op x x) := by
                first
                | (have i₁ := b26e6284
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e6284
                | exact resolve b26e6284 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6284
              have b26e6335 : False := by grind
              exact b26e6335

/-- `Equation3470`: `x ◇ x = x ◇ ((y ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation3470 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3470 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3470.models_iff G M).mp hM
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
      have b0e62 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e65 : False := by grind
      exact b0e65
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
          have b5e55 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e58 : x = y ∨ y = (k x y) := by grind
          clear b5e55
          have b5e59 : y = (k x y) := by
            first
            | (have r₁ := b5e58
               have r₂ := b5e21
               grind)
            | exact resolve b5e58 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e178 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e2503 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e178 x y
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e178
            | (have j0 := b5e178 x y
               grind)
            | exact resolve b5e178 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e178
          have b5e2506 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e2503
          have b5e2509 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e2506
               have r₂ := b5e24
               grind)
            | exact resolve b5e2506 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2506
          have b5e2513 : False := by grind
          exact b5e2513
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
          have b7e46 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e48 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e46
          have b7e49 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e49
            | exact resolve b7e49 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e50
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e50 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e26
               grind)
            | exact resolve b7e60 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e60
          have b7e62 : x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e63 : False := by grind
          exact b7e63
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
          have b8e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e121 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e130 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e121
               have r₂ := b8e24
               grind)
            | exact resolve b8e121 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121
          have b8e134 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e130
               have r₂ := b8e23
               grind)
            | exact resolve b8e130 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e135 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e134
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e134
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e134
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e134
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e134 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e136 : y = (M.op x y) ∨ x = y := by grind
          clear b8e135
          have b8e137 : x = y := by
            first
            | (have r₁ := b8e136
               have r₂ := b8e22
               grind)
            | exact resolve b8e136 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136
          have b8e138 : False := by grind
          exact b8e138
