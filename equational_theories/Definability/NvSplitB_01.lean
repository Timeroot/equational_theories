import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3736`: `x ◇ y = (x ◇ z) ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation3736 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 X0)) := by
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
      have b0e38 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 (M.op X0 X0) X2
           have i₂ := b0e11 X0 X0 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e38 X0 X1 x
           have i₂ := b0e11 X1 X0 x
           grind)
        | exact superpose b0e11 b0e38
        | exact resolve b0e38 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e44 : y = (M.op y y) := by
        first
        | (have i₁ := b0e33 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e33
        | exact resolve b0e33 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op x X0) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X1 (M.op X0 X0)
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e46 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
        intro X1
        first
        | (have i₁ := b0e45 x X1
           have i₂ := b0e11 x X1 x
           grind)
        | exact superpose b0e11 b0e45
        | exact resolve b0e45 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e103 : y = (M.op x y) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e46 y
           grind)
        | exact superpose b0e46 b0e44
        | exact resolve b0e44 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e46
      have b0e118 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e40 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e40
        | exact resolve b0e40 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e366 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e118 (σ x)
           grind)
        | exact superpose b0e118 b0e18
        | exact resolve b0e18 b0e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118
      have b0e370 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e366
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e366
        | exact resolve b0e366 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e366
      have b0e382 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e370
           have i₂ := b0e103
           grind)
        | exact superpose b0e103 b0e370
        | exact resolve b0e370 b0e103
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103 b0e370
      have b0e383 : False := by grind
      exact b0e383
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
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
        have b1e28 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 x X0 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : y = (M.op y y) := by
          first
          | (have i₁ := b1e28 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e28
          | exact resolve b1e28 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op x X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X1 (M.op X0 X0)
             have i₂ := b1e28 X0
             grind)
          | exact superpose b1e28 b1e12
          | exact resolve b1e12 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e39 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b1e38 x X1
             have i₂ := b1e12 x X1 x
             grind)
          | exact superpose b1e12 b1e38
          | exact resolve b1e38 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e97 : y = (M.op x y) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e39 y
             grind)
          | exact superpose b1e39 b1e37
          | exact resolve b1e37 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e39
        have b1e139 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e97
             grind)
          | exact superpose b1e97 b1e24
          | exact resolve b1e24 b1e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e97
        have b1e144 : False := by grind
        exact b1e144
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X0 X2) X3 (M.op X1 X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b2e28 X0 x X2 X3
             have i₂ := b2e12 X0 X3 x
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e55 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X1 X3) X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X2 X3
             have i₂ := b2e17 X2 X0
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 X0 (M.op X1 X1)
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X2 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e63 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e55 X0 X1 X2 x
             have i₂ := b2e33 X1 x X0
             grind)
          | exact superpose b2e33 b2e55
          | (have j0 := b2e55 X0 X1 X2 x
             grind)
          | exact resolve b2e55 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e55
        have b2e229 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e290 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e229
        have b2e304 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e290 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e290
          | exact resolve b2e290 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e290
        have b2e308 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e60 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e309 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e308
             have r₂ := b2e22
             grind)
          | exact resolve b2e308 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e308
        have b2e310 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e309
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e309
          | exact resolve b2e309 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e309
        have b2e311 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e310
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e310
          | exact resolve b2e310 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e310
        have b2e313 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e311
             grind)
          | exact superpose b2e311 b2e22
          | exact resolve b2e22 b2e311
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e311
        have b2e524 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e63 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e525 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e524 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e524 X1 (k X1 X1)
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e524 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e524 X0 (M.op X0 X0)
             have r₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e524 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e524
        have b2e673 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e53 x x
             grind)
          | exact superpose b2e53 b2e21
          | (have j1 := b2e53 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e53 x y
             grind)
          | exact resolve b2e21 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e732 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e673
        have b2e1490 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e732
             have i₂ := b2e525 x x
             grind)
          | exact superpose b2e525 b2e732
          | (have j1 := b2e525 (σ x) (σ x)
             grind)
          | exact resolve b2e732 b2e525
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e732
        have b2e1492 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1490
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1490
          | exact resolve b2e1490 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1490
        have b2e1493 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1492
        have b2e1497 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e1493
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1493
          | exact resolve b2e1493 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1493
        have b2e1678 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e304 x
             have i₂ := b2e1497
             grind)
          | exact superpose b2e1497 b2e304
          | exact resolve b2e304 b2e1497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e304 b2e1497
        have b2e1701 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e1678
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e1678
          | exact resolve b2e1678 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1678
        have b2e1788 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e525 x x
             have i₂ := b2e1701
             grind)
          | exact superpose b2e1701 b2e525
          | (have j0 := b2e525 x x
             grind)
          | exact resolve b2e525 b2e1701
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e525 b2e1701
        have b2e1789 : x = (M.op x x) ∨ x = y := by grind
        clear b2e1788
        have b2e1801 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e1789
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1789
          | exact resolve b2e1789 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1789
        have b2e1802 : x = y := by grind
        clear b2e1801
        have b2e1846 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e313
             have i₂ := b2e1802
             grind)
          | exact superpose b2e1802 b2e313
          | exact resolve b2e313 b2e1802
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e313 b2e1802
        have b2e1850 : False := by grind
        exact b2e1850
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 X0)) := by
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
        have b3e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X0 X2) X3 (M.op X1 X1)
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e43 X0 x X2 X3
             have i₂ := b3e12 X0 X3 x
             grind)
          | exact superpose b3e12 b3e43
          | exact resolve b3e43 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e137 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e48 (σ x) (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e48
          | exact resolve b3e48 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e189 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e42 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e42
          | exact resolve b3e42 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e200 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e189
             have i₂ := b3e137 (σ y)
             grind)
          | exact superpose b3e137 b3e189
          | exact resolve b3e189 b3e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e137 b3e189
        have b3e205 : False := by grind
        exact b3e205
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e31 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 X2 (k (τ X0) X1)
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e19
            | exact resolve b5e19 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b5e35 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X0 X2) X3 (M.op X1 X1)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 (M.op X0 X0) X2
               have i₂ := b5e13 X0 X0 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            grind
          have b5e39 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e37 X0 X1 x
               have i₂ := b5e13 X1 X0 x
               grind)
            | exact superpose b5e13 b5e37
            | exact resolve b5e37 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e40 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e36 X0 x X2 X3
               have i₂ := b5e13 X0 X3 x
               grind)
            | exact superpose b5e13 b5e36
            | exact resolve b5e36 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e42 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op x X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 y X1 (M.op X0 X0)
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e43 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b5e42 x X1
               have i₂ := b5e13 x X1 x
               grind)
            | exact superpose b5e13 b5e42
            | exact resolve b5e42 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e45 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e46 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 (M.op X0 X2) (M.op X1 X1)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 X1 (M.op (M.op X0 X2) (M.op X0 X2))
               grind)
            | (have r₁ := b5e17 (M.op X0 X2) (M.op X0 X0)
               have r₂ := b5e13 X0 X0 X2
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e45
          have b5e50 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e46 X0 X1 X2
               have i₂ := b5e40 X0 X2 (M.op X0 X2)
               grind)
            | exact superpose b5e40 b5e46
            | (have j0 := b5e46 X0 X1 X2
               grind)
            | (have r₁ := b5e46 (M.op X0 X2) X0 X2
               have r₂ := b5e40 X0 X2 X0
               grind)
            | (have r₁ := b5e46 X0 (M.op X0 X2) X2
               have r₂ := b5e40 X0 X2 (M.op X0 X2)
               grind)
            | exact resolve b5e46 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e51 : x = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e61 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X1 X3) X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X1)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e69 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e61 X0 X1 X2 x
               have i₂ := b5e40 X1 x X0
               grind)
            | exact superpose b5e40 b5e61
            | (have j0 := b5e61 X0 X1 X2 x
               grind)
            | exact resolve b5e61 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e78 : y = (k y (M.op x y)) := by grind
          have b5e83 : y = (k y y) := by
            first
            | (have i₁ := b5e78
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e78
            | exact resolve b5e78 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e132 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e39 (M.op X0 X1) X2
               have i₂ := b5e40 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b5e40 b5e39
            | exact resolve b5e39 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e133 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 (M.op X0 X1) X2
               have i₂ := b5e40 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b5e40 b5e18
            | (have j0 := b5e18 (M.op X0 X1) X2
               grind)
            | exact resolve b5e18 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e136 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            grind
          have b5e137 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = X1 ∨ (M.op X0 X2) = (k (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 (M.op X0 X2) X1
               have i₂ := b5e40 X0 X2 X1
               grind)
            | exact superpose b5e40 b5e17
            | (have j0 := b5e17 (M.op X0 X2) X1
               grind)
            | exact resolve b5e17 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e142 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 (M.op X0 X2)) = X1 ∨ (M.op X0 X2) = (k (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e137 X0 X1 X2
               have i₂ := b5e40 X0 X2 (M.op X0 X2)
               grind)
            | exact superpose b5e40 b5e137
            | (have j0 := b5e137 X0 X1 X2
               grind)
            | exact resolve b5e137 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e137
          have b5e145 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e133 X0 X1 X2
               have i₂ := b5e40 X0 X1 X2
               grind)
            | exact superpose b5e40 b5e133
            | (have j0 := b5e133 X0 X1 X2
               grind)
            | exact resolve b5e133 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e133
          have b5e152 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e145 X0 X1 X2
               have i₂ := b5e40 X0 X1 X2
               grind)
            | exact superpose b5e40 b5e145
            | (have j0 := b5e145 X0 X1 X2
               grind)
            | exact resolve b5e145 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e145
          have b5e160 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e166 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e38 (M.op X0 x)
               have i₂ := b5e40 X0 x (M.op X0 x)
               grind)
            | exact superpose b5e40 b5e38
            | exact resolve b5e38 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e174 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e33
            | exact resolve b5e33 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e212 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e213 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e212
               have r₂ := b5e24
               grind)
            | exact resolve b5e212 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e212
          have b5e214 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e213
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e213
            | exact resolve b5e213 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213
          have b5e215 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e214
               have i₂ := b5e51
               grind)
            | exact superpose b5e51 b5e214
            | exact resolve b5e214 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e214
          have b5e216 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e215
               grind)
            | exact superpose b5e215 b5e24
            | exact resolve b5e24 b5e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e387 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e69 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e388 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e387 X0 X1
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e387 X1 (k X1 X1)
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e387 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e387 X0 (M.op X0 X0)
               have r₂ := b5e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b5e387 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e387
          have b5e514 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b5e516 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e38 (σ x)
               have i₂ := b5e57 x x
               grind)
            | exact superpose b5e57 b5e38
            | (have j1 := b5e57 X0 X0
               grind)
            | exact resolve b5e38 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e550 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e57 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e552 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e550 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e550
          have b5e556 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e516 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e516
          have b5e558 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e514 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e514
          have b5e574 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e556 X0
               have i₂ := b5e19 (k X0 X0) (k X0 X0)
               grind)
            | exact superpose b5e19 b5e556
            | (have j0 := b5e556 X0
               grind)
            | exact resolve b5e556 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e556
          have b5e576 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e558 X0
               have i₂ := b5e19 X0 (k X0 X0)
               grind)
            | exact superpose b5e19 b5e558
            | (have j0 := b5e558 X0
               grind)
            | exact resolve b5e558 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e558
          have b5e635 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e50 X0 X0 X2
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e50 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b5e18 b5e50
            | (have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e50 X0 X0 X2
               have r₂ := b5e18 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b5e50 X0 X0 X2
               have r₂ := b5e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b5e50 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e657 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e50 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e660 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e635 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e635
          have b5e668 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e660 X0 X1 X2
               have j1 := b5e142 X1 X0 X2
               grind)
            | (have r₁ := b5e660 (M.op X0 X2) X0 X2
               have r₂ := b5e142 X0 (M.op X0 X2) X2
               grind)
            | (have r₁ := b5e660 (M.op X0 (M.op X1 (M.op X1 X2))) X1 X2
               have r₂ := b5e142 X0 (M.op X1 (M.op X1 X2)) X2
               grind)
            | (have r₁ := b5e660 X1 X0 X2
               have r₂ := b5e142 X0 X1 X2
               grind)
            | exact resolve b5e660 b5e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e142 b5e660
          have b5e695 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X0 X1
               have i₂ := b5e388 X0 (σ X1)
               grind)
            | exact superpose b5e388 b5e33
            | (have j1 := b5e388 X0 (σ X1)
               grind)
            | exact resolve b5e33 b5e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e701 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e388 (σ X0) (σ X1)
               grind)
            | exact superpose b5e388 b5e19
            | (have j1 := b5e388 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e702 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e160 X0 X1
               have i₂ := b5e388 (σ X0) X1
               grind)
            | exact superpose b5e388 b5e160
            | (have j1 := b5e388 (σ X0) X1
               grind)
            | exact resolve b5e160 b5e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e160 b5e388
          have b5e808 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X0) = (M.op X1 (M.op X1 X2)) ∨ (k X0 (M.op X1 (M.op X1 X2))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X0 (M.op X1 (M.op X1 X2))
               have i₂ := b5e132 X1 X2 X0
               grind)
            | exact superpose b5e132 b5e17
            | (have j0 := b5e17 X0 (M.op X1 (M.op X1 X2))
               grind)
            | (have r₁ := b5e17 X2 (M.op X2 (M.op X2 X1))
               have r₂ := b5e132 X2 X1 X2
               grind)
            | exact resolve b5e17 b5e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132
          have b5e1247 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e552 y
               have i₂ := b5e83
               grind)
            | exact superpose b5e83 b5e552
            | (have j0 := b5e552 y
               grind)
            | exact resolve b5e552 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e1251 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e1247
          have b5e1591 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 (k (τ X0) (τ X0))
               have i₂ := b5e576 (τ X0)
               grind)
            | exact superpose b5e576 b5e27
            | (have j1 := b5e576 (τ X0)
               grind)
            | exact resolve b5e27 b5e576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e576
          have b5e1625 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e1591 X0
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e1591
            | (have j0 := b5e1591 X0
               grind)
            | exact resolve b5e1591 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1591
          have b5e1637 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e1625 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1625
            | (have j0 := b5e1625 X0
               grind)
            | exact resolve b5e1625 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1625
          have b5e1640 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1637 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1637
            | (have j0 := b5e1637 X0
               grind)
            | exact resolve b5e1637 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1637
          have b5e1677 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 (k (τ X0) (τ X0))
               have i₂ := b5e1640 (τ X0)
               grind)
            | exact superpose b5e1640 b5e27
            | (have j1 := b5e1640 (τ X0)
               grind)
            | exact resolve b5e27 b5e1640
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e1640
          have b5e1684 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e1677 X0
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e1677
            | (have j0 := b5e1677 X0
               grind)
            | exact resolve b5e1677 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1677
          have b5e1696 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e1684 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1684
            | (have j0 := b5e1684 X0
               grind)
            | exact resolve b5e1684 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1684
          have b5e2310 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e657 y x
               have i₂ := b5e43 y
               grind)
            | exact superpose b5e43 b5e657
            | exact resolve b5e657 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e657
          have b5e2336 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) y) ∨ (M.op x y) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e2310 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2310
            | (have j0 := b5e2310 X0
               grind)
            | exact resolve b5e2310 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2310
          have b5e2346 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) y) ∨ (M.op x y) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e2336 x
               have i₂ := b5e43 x
               grind)
            | exact superpose b5e43 b5e2336
            | (have j0 := b5e2336 X0
               grind)
            | exact resolve b5e2336 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2336
          have b5e2355 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y X0)) ∨ (M.op x X0) = (k (M.op x X0) y) := by
            intro X0
            first
            | (have i₁ := b5e2346 X0
               have i₂ := b5e43 (M.op y X0)
               grind)
            | exact superpose b5e43 b5e2346
            | (have j0 := b5e2346 X0
               grind)
            | exact resolve b5e2346 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2346
          have b5e2364 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) ∨ (M.op x X0) = (k (M.op x X0) y) := by
            intro X0
            first
            | (have i₁ := b5e2355 X0
               have i₂ := b5e43 X0
               grind)
            | exact superpose b5e43 b5e2355
            | (have j0 := b5e2355 X0
               grind)
            | exact resolve b5e2355 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2355
          have b5e2369 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) y) ∨ y = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e2364 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2364
            | (have j0 := b5e2364 X0
               grind)
            | exact resolve b5e2364 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2364
          have b5e2782 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e166 X0 (M.op X0 X1)
               have i₂ := b5e152 X0 X1 X2
               grind)
            | (have i₁ := b5e166 X0 X1
               have i₂ := b5e152 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b5e152 b5e166
            | (have j1 := b5e152 X1 X2 X0
               grind)
            | exact resolve b5e166 b5e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e166
          have b5e4269 : ∀ X0 : G, (σ (τ (k X0 X0))) = (σ (k (τ (k X0 X0)) (τ (k X0 X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e574 (τ X0)
               have i₂ := b5e174 X0 X0
               grind)
            | exact superpose b5e174 b5e574
            | (have j0 := b5e574 (τ X0)
               grind)
            | exact resolve b5e574 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e574
          have b5e4324 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e4269 X0
               have i₂ := b5e28 (k X0 X0) (τ (k X0 X0))
               grind)
            | exact superpose b5e28 b5e4269
            | (have j0 := b5e4269 X0
               grind)
            | exact resolve b5e4269 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4269
          have b5e4332 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e4324 X0
               have i₂ := b5e15 (k X0 X0)
               grind)
            | exact superpose b5e15 b5e4324
            | (have j0 := b5e4324 X0
               grind)
            | exact resolve b5e4324 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4324
          have b5e4333 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4332 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e4332
            | (have j0 := b5e4332 X0
               grind)
            | exact resolve b5e4332 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4332
          have b5e4377 : ∀ X0 : G, (σ X0) = (σ (k X0 (k (τ (σ X0)) X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e31 (σ X0) X0 X0
               have i₂ := b5e1696 (σ X0)
               grind)
            | exact superpose b5e1696 b5e31
            | (have j1 := b5e1696 (σ X0)
               grind)
            | exact resolve b5e31 b5e1696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e1696
          have b5e4397 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e4377 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e4377
            | (have j0 := b5e4377 X0
               grind)
            | exact resolve b5e4377 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4377
          have b5e4413 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4397 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e4397
            | (have j0 := b5e4397 X0
               grind)
            | exact resolve b5e4397 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4397
          have b5e4551 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e702 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e702
            | exact resolve b5e702 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e702
          have b5e4596 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e4551 X0 X1
               have i₂ := b5e174 X1 X0
               grind)
            | exact superpose b5e174 b5e4551
            | (have j0 := b5e4551 X0 X1
               grind)
            | exact resolve b5e4551 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4551
          have b5e4673 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e174 X2 (k X0 X1)
               have i₂ := b5e4596 X0 X1
               grind)
            | exact superpose b5e4596 b5e174
            | (have j1 := b5e4596 X0 X1
               grind)
            | exact resolve b5e174 b5e4596
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4596
          have b5e4675 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e4673 X0 X1 X2
               have i₂ := b5e174 X2 (M.op X0 X1)
               grind)
            | exact superpose b5e174 b5e4673
            | (have j0 := b5e4673 X0 X1 X2
               grind)
            | exact resolve b5e4673 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4673
          have b5e5668 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e552 (k X0 X0)
               have i₂ := b5e4333 X0
               grind)
            | exact superpose b5e4333 b5e552
            | (have j0 := b5e552 (k X0 X0)
               have j1 := b5e4333 (σ (k X0 X0))
               grind)
            | exact resolve b5e552 b5e4333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e552 b5e4333
          have b5e5690 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e5668 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5668
          have b5e6426 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op x (σ X0))) ∨ (σ X0) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e695 y x
               have i₂ := b5e43 (σ x)
               grind)
            | exact superpose b5e43 b5e695
            | (have j0 := b5e695 x X0
               grind)
            | exact resolve b5e695 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7744 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e136 X1 X2
               have i₂ := b5e668 X0 X1 X2
               grind)
            | (have i₁ := b5e136 X0 X1
               have i₂ := b5e668 (M.op X0 (M.op X0 X1)) X1 X2
               grind)
            | exact superpose b5e668 b5e136
            | (have j1 := b5e668 X0 X1 X2
               grind)
            | exact resolve b5e136 b5e668
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e136 b5e668
          have b5e7794 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e7744 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7744
          have b5e8342 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) X3) ∨ (M.op (M.op X0 X2) X3) = (k (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e7794 X0 (M.op X0 X2) X3
               have i₂ := b5e40 X0 X2 X3
               grind)
            | exact superpose b5e40 b5e7794
            | (have j0 := b5e7794 X3 X0 X1
               grind)
            | exact resolve b5e7794 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e8349 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e7794 X0 (σ x) (σ y)
               have i₂ := b5e215
               grind)
            | exact superpose b5e215 b5e7794
            | (have j0 := b5e7794 X0 (σ x) x
               grind)
            | exact resolve b5e7794 b5e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e8361 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op x X0) X1) ∨ (M.op y X1) = (k y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e7794 X0 y X1
               have i₂ := b5e43 X1
               grind)
            | exact superpose b5e43 b5e7794
            | (have j0 := b5e7794 X1 x X0
               grind)
            | exact resolve b5e7794 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e8412 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X1)) X2) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 (M.op X0 X1) X2
               have i₂ := b5e7794 (σ X2) X0 X1
               grind)
            | exact superpose b5e7794 b5e33
            | (have j1 := b5e7794 (σ X2) X0 X2
               grind)
            | exact resolve b5e33 b5e7794
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7794
          have b5e8444 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op x X0) X1) ∨ (M.op x X1) = (k y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e8361 X0 X1
               have i₂ := b5e43 X1
               grind)
            | exact superpose b5e43 b5e8361
            | (have j0 := b5e8361 X0 X1
               grind)
            | exact resolve b5e8361 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8361
          have b5e8446 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k (M.op X0 X2) X3) ∨ (M.op X0 X1) = (k (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e8342 X0 X1 X2 X3
               have i₂ := b5e40 X0 X2 X3
               grind)
            | exact superpose b5e40 b5e8342
            | (have j0 := b5e8342 X0 X1 X2 X3
               grind)
            | exact resolve b5e8342 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8342
          have b5e9088 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b5e8349 (σ x)
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e8349
            | exact resolve b5e8349 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8349
          have b5e9976 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e8444 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e8444
            | (have j0 := b5e8444 X0 X0
               grind)
            | exact resolve b5e8444 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8444
          have b5e10430 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op x (σ X0))) ∨ y = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e33 y X0
               have i₂ := b5e9976 (σ X0)
               grind)
            | exact superpose b5e9976 b5e33
            | (have j1 := b5e9976 (σ X0)
               grind)
            | exact resolve b5e33 b5e9976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e10434 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op x (τ X0))) ∨ y = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e28 X0 y
               have i₂ := b5e9976 (τ X0)
               grind)
            | exact superpose b5e9976 b5e28
            | (have j1 := b5e9976 (τ X0)
               grind)
            | exact resolve b5e28 b5e9976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e10447 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k y X0) := by
            intro X0
            first
            | (have j0 := b5e9976 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9976
          have b5e16326 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op x X0)) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e10434 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e10434
            | exact resolve b5e10434 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10434
          have b5e16410 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op x X0)) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e16326 X0
               have i₂ := b5e19 y X0
               grind)
            | exact superpose b5e19 b5e16326
            | (have j0 := b5e16326 X0
               grind)
            | exact resolve b5e16326 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16326
          have b5e23491 : ∀ X0 : G, (τ (M.op x X0)) = (k (τ y) (τ X0)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e6426 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e6426
            | exact resolve b5e6426 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e23528 : ∀ X0 : G, (k (τ y) X0) = (k (τ x) X0) ∨ (σ X0) = (M.op x (σ X0)) ∨ (σ X0) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e695 x X0
               have i₂ := b5e6426 X0
               grind)
            | exact superpose b5e6426 b5e695
            | (have j0 := b5e695 x X0
               have j1 := b5e6426 X0
               grind)
            | exact resolve b5e695 b5e6426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e695 b5e6426
          have b5e23554 : ∀ X0 : G, (k (τ y) X0) = (k (τ x) X0) ∨ (σ X0) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e23528 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23528
          have b5e23557 : ∀ X0 : G, (τ (k y X0)) = (τ (M.op x X0)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23491 X0
               have i₂ := b5e174 X0 y
               grind)
            | exact superpose b5e174 b5e23491
            | (have j0 := b5e23491 X0
               grind)
            | exact resolve b5e23491 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23491
          have b5e24539 : ∀ X0 : G, (k y X0) = (σ (τ (M.op x X0))) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e15 (k y X0)
               have i₂ := b5e23557 X0
               grind)
            | exact superpose b5e23557 b5e15
            | (have j1 := b5e23557 X0
               grind)
            | exact resolve b5e15 b5e23557
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e24548 : ∀ X0 X1 : G, (τ (k (k y X0) X1)) = (k (τ (M.op x X0)) (τ X1)) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e174 X1 (k y X0)
               have i₂ := b5e23557 X0
               grind)
            | exact superpose b5e23557 b5e174
            | (have j1 := b5e23557 X0
               grind)
            | exact resolve b5e174 b5e23557
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23557
          have b5e24564 : ∀ X0 X1 : G, (τ (k (M.op x X0) X1)) = (τ (k (k y X0) X1)) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e24548 X0 X1
               have i₂ := b5e174 X1 (M.op x X0)
               grind)
            | exact superpose b5e174 b5e24548
            | (have j0 := b5e24548 X0 X1
               grind)
            | exact resolve b5e24548 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24548
          have b5e24568 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e24539 X0
               have i₂ := b5e15 (M.op x X0)
               grind)
            | exact superpose b5e15 b5e24539
            | (have j0 := b5e24539 X0
               grind)
            | exact resolve b5e24539 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24539
          have b5e26002 : ∀ X0 : G, (τ (k y X0)) = (k (τ x) (τ X0)) ∨ (σ (τ X0)) = (M.op x (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e174 X0 y
               have i₂ := b5e23554 (τ X0)
               grind)
            | exact superpose b5e23554 b5e174
            | (have j1 := b5e23554 (τ X0)
               grind)
            | exact resolve b5e174 b5e23554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23554
          have b5e26115 : ∀ X0 : G, (τ (k y X0)) = (τ (k x X0)) ∨ (σ (τ X0)) = (M.op x (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e26002 X0
               have i₂ := b5e174 X0 x
               grind)
            | exact superpose b5e174 b5e26002
            | (have j0 := b5e26002 X0
               grind)
            | exact resolve b5e26002 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26002
          have b5e26143 : ∀ X0 : G, (τ (k y X0)) = (τ (k x X0)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e26115 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e26115
            | (have j0 := b5e26115 X0
               grind)
            | exact resolve b5e26115 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26115
          have b5e28535 : ∀ X0 X1 : G, (τ (k (k y X0) X1)) = (k (τ (k x X0)) (τ X1)) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e174 X1 (k y X0)
               have i₂ := b5e26143 X0
               grind)
            | exact superpose b5e26143 b5e174
            | (have j1 := b5e26143 X0
               grind)
            | exact resolve b5e174 b5e26143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26143
          have b5e28555 : ∀ X0 X1 : G, (τ (k (k y X0) X1)) = (τ (k (k x X0) X1)) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e28535 X0 X1
               have i₂ := b5e174 X1 (k x X0)
               grind)
            | exact superpose b5e174 b5e28535
            | (have j0 := b5e28535 X0 X1
               grind)
            | exact resolve b5e28535 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28535
          have b5e35120 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ (k x X0)) X1) ∨ (σ x) = (σ (k x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 (σ x) (σ X0) X1
               have i₂ := b5e9088 X0
               grind)
            | exact superpose b5e9088 b5e40
            | (have j1 := b5e9088 X0
               grind)
            | exact resolve b5e40 b5e9088
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9088
          have b5e40880 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40 (σ X0) (σ X1) X2
               have i₂ := b5e701 X0 X1
               grind)
            | exact superpose b5e701 b5e40
            | (have j1 := b5e701 X0 X1
               grind)
            | exact resolve b5e40 b5e701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40949 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e701 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e701
          have b5e41107 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e40949 X0 (k X0 X0)
               have i₂ := b5e4413 X0
               grind)
            | exact superpose b5e4413 b5e40949
            | (have j0 := b5e40949 X0 X0
               have j1 := b5e4413 X0
               grind)
            | exact resolve b5e40949 b5e4413
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4413 b5e40949
          have b5e67700 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op x X1) X0) ∨ y = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e8446 x y x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e8446
            | (have j0 := b5e8446 x X1 X1 X0
               grind)
            | exact resolve b5e8446 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68041 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e8446 X0 X1 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8446
          have b5e68780 : ∀ X0 X1 : G, (τ (M.op x (σ X0))) = (k (τ (M.op x X1)) X0) ∨ y = (k y (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 (M.op x X1) X0
               have i₂ := b5e67700 (σ X0) X1
               grind)
            | exact superpose b5e67700 b5e33
            | (have j1 := b5e67700 (σ X0) X1
               grind)
            | exact resolve b5e33 b5e67700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67700
          have b5e73872 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (M.op (σ x) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e68041 (σ x) x (σ y)
               have i₂ := b5e215
               grind)
            | exact superpose b5e215 b5e68041
            | exact resolve b5e68041 b5e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68041
          have b5e117545 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) X0) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e2782 (σ y) (σ x) x
               have i₂ := b5e215
               grind)
            | exact superpose b5e215 b5e2782
            | exact resolve b5e2782 b5e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2782
          have b5e118122 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) X0) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e117545 X0
               grind)
            | (have r₁ := b5e117545 X0
               have r₂ := b5e216
               grind)
            | exact resolve b5e117545 b5e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e117545
          have b5e118146 : ∀ X0 : G, (σ x) = (k (M.op (σ x) X0) (σ y)) ∨ (σ x) = (σ (k x x)) := by
            intro X0
            first
            | (have i₁ := b5e118122 X0
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e118122
            | (have j0 := b5e118122 X0
               grind)
            | exact resolve b5e118122 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118122
          have b5e160739 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (σ (τ (k (M.op X0 X1) X2))) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e15 (k (k X0 X1) X2)
               have i₂ := b5e4675 X0 X1 X2
               grind)
            | exact superpose b5e4675 b5e15
            | (have j1 := b5e4675 X0 X1 X2
               grind)
            | exact resolve b5e15 b5e4675
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4675
          have b5e160866 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (k (k X0 X1) X2) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e160739 X0 X1 X2
               have i₂ := b5e15 (k (M.op X0 X1) X2)
               grind)
            | exact superpose b5e15 b5e160739
            | (have j0 := b5e160739 X0 X1 X2
               grind)
            | exact resolve b5e160739 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e160739
          have b5e220586 : ∀ X0 X1 : G, (k (k y X0) X1) = (σ (τ (k (M.op x X0) X1))) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e15 (k (k y X0) X1)
               have i₂ := b5e24564 X0 X1
               grind)
            | exact superpose b5e24564 b5e15
            | (have j1 := b5e24564 X0 X1
               grind)
            | exact resolve b5e15 b5e24564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24564
          have b5e220723 : ∀ X0 X1 : G, (k (M.op x X0) X1) = (k (k y X0) X1) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e220586 X0 X1
               have i₂ := b5e15 (k (M.op x X0) X1)
               grind)
            | exact superpose b5e15 b5e220586
            | (have j0 := b5e220586 X0 X1
               grind)
            | exact resolve b5e220586 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e220586
          have b5e229087 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e808 X0 X0 X1
               have i₂ := b5e152 X0 X1 X2
               grind)
            | (have i₁ := b5e808 X0 X1 X2
               have i₂ := b5e152 X0 X1 (M.op X0 (M.op X1 X2))
               grind)
            | exact superpose b5e152 b5e808
            | (have j1 := b5e152 X1 X2 X0
               grind)
            | (have r₁ := b5e808 X0 X0 X1
               have r₂ := b5e152 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | (have r₁ := b5e808 X0 X0 X1
               have r₂ := b5e152 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact resolve b5e808 b5e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e152 b5e808
          have b5e229220 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e229087 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e229087
          have b5e229234 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e229220 X0 X1 X2
               have j1 := b5e17 X1 X0
               grind)
            | (have r₁ := b5e229220 X1 X1 X2
               have r₂ := b5e17 X1 X1
               grind)
            | (have r₁ := b5e229220 (M.op X0 (M.op X1 X1)) X1 X2
               have r₂ := b5e17 X0 (M.op X1 X1)
               grind)
            | (have r₁ := b5e229220 X1 X0 X2
               have r₂ := b5e17 X0 X1
               grind)
            | exact resolve b5e229220 b5e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e229220
          have b5e286833 : ∀ X0 X1 : G, (k (k y X0) X1) = (σ (τ (k (k x X0) X1))) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e15 (k (k y X0) X1)
               have i₂ := b5e28555 X0 X1
               grind)
            | exact superpose b5e28555 b5e15
            | (have j1 := b5e28555 X0 X1
               grind)
            | exact resolve b5e15 b5e28555
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28555
          have b5e286987 : ∀ X0 X1 : G, (k (k x X0) X1) = (k (k y X0) X1) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e286833 X0 X1
               have i₂ := b5e15 (k (k x X0) X1)
               grind)
            | exact superpose b5e15 b5e286833
            | (have j0 := b5e286833 X0 X1
               grind)
            | exact resolve b5e286833 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e286833
          have b5e766922 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40880 (τ X0) (τ X1) X2
               have i₂ := b5e174 X1 X0
               grind)
            | exact superpose b5e174 b5e40880
            | (have j0 := b5e40880 (τ X0) (τ X1) X2
               grind)
            | exact resolve b5e40880 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e174 b5e40880
          have b5e767019 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e766922 X0 X1 X2
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e766922
            | (have j0 := b5e766922 X0 X1 X2
               grind)
            | exact resolve b5e766922 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e766922
          have b5e767021 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e767019 X0 X1 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e767019
            | (have j0 := b5e767019 X0 X1 X2
               grind)
            | exact resolve b5e767019 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e767019
          have b5e767022 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e767021 X0 X0 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e767021
            | (have j0 := b5e767021 X0 X1 X2
               grind)
            | exact resolve b5e767021 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e767021
          have b5e767023 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e767022 X0 X1 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e767022
            | (have j0 := b5e767022 X0 X1 X2
               grind)
            | exact resolve b5e767022 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e767022
          have b5e772002 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) (M.op X0 (k X0 X1))) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          clear b5e767023
          have b5e782726 : ∀ X0 : G, (k y X0) = (k (M.op x X0) (M.op y (k y X0))) ∨ (M.op x X0) = X0 ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e220723 X0 (M.op y (k y X0))
               have i₂ := b5e772002 y X0
               grind)
            | exact superpose b5e772002 b5e220723
            | (have j0 := b5e220723 X0 x
               have j1 := b5e772002 x X0
               grind)
            | exact resolve b5e220723 b5e772002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e220723
          have b5e782727 : ∀ X0 : G, (k y X0) = (k (k x X0) (M.op y (k y X0))) ∨ (M.op x X0) = X0 ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e286987 X0 (M.op y (k y X0))
               have i₂ := b5e772002 y X0
               grind)
            | exact superpose b5e772002 b5e286987
            | (have j0 := b5e286987 X0 x
               have j1 := b5e772002 x X0
               grind)
            | exact resolve b5e286987 b5e772002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e286987
          have b5e782731 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X1) (M.op X0 (k X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e160866 X0 X1 (M.op X0 (k X0 X1))
               have i₂ := b5e772002 X0 X1
               grind)
            | exact superpose b5e772002 b5e160866
            | (have j0 := b5e160866 X0 X1 x
               have j1 := b5e772002 X0 X1
               grind)
            | exact resolve b5e160866 b5e772002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e772002
          have b5e782735 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X1) (M.op X0 (k X0 X1))) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e782731 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782731
          have b5e782744 : ∀ X0 : G, (k y X0) = (k (k x X0) (M.op x (k y X0))) ∨ (M.op x X0) = X0 ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e782727 X0
               have i₂ := b5e43 (k y X0)
               grind)
            | exact superpose b5e43 b5e782727
            | (have j0 := b5e782727 X0
               grind)
            | exact resolve b5e782727 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782727
          have b5e782745 : ∀ X0 : G, (k y X0) = (k (M.op x X0) (M.op x (k y X0))) ∨ (M.op x X0) = X0 ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e782726 X0
               have i₂ := b5e43 (k y X0)
               grind)
            | exact superpose b5e43 b5e782726
            | (have j0 := b5e782726 X0
               grind)
            | exact resolve b5e782726 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782726
          have b5e782770 : ∀ X0 : G, (M.op x X0) = X0 ∨ (k y X0) = (k (k x X0) (M.op x (k y X0))) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e782744 X0
               have i₂ := b5e43 X0
               grind)
            | exact superpose b5e43 b5e782744
            | (have j0 := b5e782744 X0
               grind)
            | exact resolve b5e782744 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782744
          have b5e782771 : ∀ X0 : G, (k y X0) = (k (k x X0) (M.op x (k y X0))) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e782770 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782770
          have b5e782772 : ∀ X0 : G, (M.op x X0) = X0 ∨ (k y X0) = (k (M.op x X0) (M.op x (k y X0))) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e782745 X0
               have i₂ := b5e43 X0
               grind)
            | exact superpose b5e43 b5e782745
            | (have j0 := b5e782745 X0
               grind)
            | exact resolve b5e782745 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e782745
          have b5e782773 : ∀ X0 : G, (k y X0) = (k (M.op x X0) (M.op x (k y X0))) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e782772 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782772
          have b5e879327 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1 X2
            grind
          clear b5e229234
          have b5e879361 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e879327 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e879327
          have b5e880066 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b5e879361 X0 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e879361
            | (have j0 := b5e879361 X0 x x
               grind)
            | exact resolve b5e879361 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e880195 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 X2)) X1) ∨ (k X0 (τ X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e28 X1 (M.op X0 X2)
               have i₂ := b5e879361 (τ X1) X0 X2
               grind)
            | exact superpose b5e879361 b5e28
            | (have j1 := b5e879361 (τ X1) X0 X2
               grind)
            | exact resolve b5e28 b5e879361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e879361
          have b5e940316 : ∀ X0 X1 X2 : G, (σ (k (M.op X0 X2) X1)) = (σ (M.op X0 (τ (σ X1)))) ∨ (k X0 (τ (σ X1))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 (M.op X0 X2) X1
               have i₂ := b5e880195 X0 (σ X1) X2
               grind)
            | exact superpose b5e880195 b5e19
            | (have j1 := b5e880195 X0 (σ X1) X2
               grind)
            | exact resolve b5e19 b5e880195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e880195
          have b5e940340 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (σ (k (M.op X0 X2) X1)) ∨ (k X0 (τ (σ X1))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e940316 X0 X1 X2
               have i₂ := b5e14 X1
               grind)
            | exact superpose b5e14 b5e940316
            | (have j0 := b5e940316 X0 X1 X2
               grind)
            | exact resolve b5e940316 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e940316
          have b5e940366 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (σ (k (M.op X0 X2) X1)) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e940340 X0 X1 X2
               have i₂ := b5e14 X1
               grind)
            | exact superpose b5e14 b5e940340
            | (have j0 := b5e940340 X0 X1 X2
               grind)
            | exact resolve b5e940340 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e940340
          have b5e1017169 : (σ (k x x)) = (M.op (σ x) (σ (k x x))) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e35120 x (σ (k x x))
               have i₂ := b5e5690 x
               grind)
            | exact superpose b5e5690 b5e35120
            | (have j0 := b5e35120 x x
               have j1 := b5e5690 x
               grind)
            | exact resolve b5e35120 b5e5690
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5690 b5e35120
          have b5e1017217 : (σ (k x x)) = (M.op (σ x) (σ (k x x))) ∨ x = (M.op x x) := by
            first
            | (have j1 := b5e41107 x
               grind)
            | (have r₁ := b5e1017169
               have r₂ := b5e41107 x
               grind)
            | exact resolve b5e1017169 b5e41107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41107 b5e1017169
          have b5e1022277 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ (k x x)) (σ y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e73872 (σ (k x x))
               have i₂ := b5e1017217
               grind)
            | exact superpose b5e1017217 b5e73872
            | exact resolve b5e73872 b5e1017217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73872
          have b5e1022279 : (σ x) = (k (σ (k x x)) (σ y)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e118146 (σ (k x x))
               have i₂ := b5e1017217
               grind)
            | exact superpose b5e1017217 b5e118146
            | exact resolve b5e118146 b5e1017217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118146 b5e1017217
          have b5e1022341 : (σ x) = (σ (k (k x x) y)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1022279
               have i₂ := b5e19 (k x x) y
               grind)
            | exact superpose b5e19 b5e1022279
            | exact resolve b5e1022279 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1022279
          have b5e1022343 : (σ x) = (σ (k (k x x) y)) ∨ (σ x) ≠ (σ (k x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1022277
               have i₂ := b5e19 (k x x) y
               grind)
            | exact superpose b5e19 b5e1022277
            | exact resolve b5e1022277 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1022277
          have b5e1022353 : (σ x) = (σ (k (k x x) y)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b5e1022343
               have r₂ := b5e1022341
               grind)
            | exact resolve b5e1022343 b5e1022341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1022341 b5e1022343
          have b5e1022795 : (τ (σ x)) = (k (k x x) y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e14 (k (k x x) y)
               have i₂ := b5e1022353
               grind)
            | exact superpose b5e1022353 b5e14
            | exact resolve b5e14 b5e1022353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1022353
          have b5e1022885 : x = (k (k x x) y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1022795
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e1022795
            | exact resolve b5e1022795 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1022795
          have b5e1027976 : x = (k (M.op x x) y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e160866 x x y
               have i₂ := b5e1022885
               grind)
            | exact superpose b5e1022885 b5e160866
            | (have j0 := b5e160866 x x x
               grind)
            | exact resolve b5e160866 b5e1022885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e160866 b5e1022885
          have b5e1028017 : x = (k (M.op x x) y) ∨ x = (M.op x x) := by grind
          clear b5e1027976
          have b5e1028062 : x = (M.op x x) ∨ y = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e2369 x
               have i₂ := b5e1028017
               grind)
            | exact superpose b5e1028017 b5e2369
            | (have j0 := b5e2369 x
               grind)
            | exact resolve b5e2369 b5e1028017
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1028017
          have b5e1028155 : x = (M.op x x) ∨ y = (M.op x (M.op x x)) := by grind
          clear b5e1028062
          have b5e1028200 : y = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1028155
               have i₂ := b5e39 x x
               grind)
            | exact superpose b5e39 b5e1028155
            | exact resolve b5e1028155 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e1028155
          have b5e1028237 : x = (M.op x x) := by
            first
            | (have r₁ := b5e1028200
               have r₂ := b5e21
               grind)
            | exact resolve b5e1028200 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1028200
          have b5e1029444 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e1028237
               grind)
            | exact superpose b5e1028237 b5e21
            | exact resolve b5e21 b5e1028237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1029455 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ x) X0) ∨ y = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e68780 X0 x
               have i₂ := b5e1028237
               grind)
            | exact superpose b5e1028237 b5e68780
            | (have j0 := b5e68780 X0 x
               grind)
            | exact resolve b5e68780 b5e1028237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68780
          have b5e1029642 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b5e940366 x X0 x
               have i₂ := b5e1028237
               grind)
            | exact superpose b5e1028237 b5e940366
            | (have j0 := b5e940366 x X0 x
               grind)
            | exact resolve b5e940366 b5e1028237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e940366 b5e1028237
          have b5e1140322 : ∀ X0 : G, (k (τ y) X0) = (k (τ x) X0) ∨ y = (k y (σ X0)) ∨ y = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e10430 X0
               have i₂ := b5e1029455 X0
               grind)
            | exact superpose b5e1029455 b5e10430
            | (have j0 := b5e10430 X0
               have j1 := b5e1029455 X0
               grind)
            | exact resolve b5e10430 b5e1029455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10430 b5e1029455
          have b5e1140339 : ∀ X0 : G, (k (τ y) X0) = (k (τ x) X0) ∨ y = (k y (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e1140322 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1140322
          have b5e1147367 : ∀ X0 : G, (k (σ (τ y)) X0) = (σ (k (τ x) (τ X0))) ∨ y = (k y (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e28 X0 (τ y)
               have i₂ := b5e1140339 (τ X0)
               grind)
            | exact superpose b5e1140339 b5e28
            | (have j1 := b5e1140339 (τ X0)
               grind)
            | exact resolve b5e28 b5e1140339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1140339
          have b5e1147380 : ∀ X0 : G, (k (σ (τ y)) X0) = (k (σ (τ x)) X0) ∨ y = (k y (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e1147367 X0
               have i₂ := b5e28 X0 (τ x)
               grind)
            | exact superpose b5e28 b5e1147367
            | (have j0 := b5e1147367 X0
               grind)
            | exact resolve b5e1147367 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1147367
          have b5e1147401 : ∀ X0 : G, (k x X0) = (k (σ (τ y)) X0) ∨ y = (k y (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e1147380 X0
               have i₂ := b5e15 x
               grind)
            | exact superpose b5e15 b5e1147380
            | (have j0 := b5e1147380 X0
               grind)
            | exact resolve b5e1147380 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1147380
          have b5e1147406 : ∀ X0 : G, (k x X0) = (k y X0) ∨ y = (k y (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e1147401 X0
               have i₂ := b5e15 y
               grind)
            | exact superpose b5e15 b5e1147401
            | (have j0 := b5e1147401 X0
               grind)
            | exact resolve b5e1147401 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1147401
          have b5e1147409 : ∀ X0 : G, (k x X0) = (k y X0) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e1147406 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1147406
            | (have j0 := b5e1147406 X0
               grind)
            | exact resolve b5e1147406 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1147406
          have b5e1149187 : ∀ X0 : G, (k (σ y) X0) = (σ (k x (τ X0))) ∨ y = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e28 X0 y
               have i₂ := b5e1147409 (τ X0)
               grind)
            | exact superpose b5e1147409 b5e28
            | (have j1 := b5e1147409 (τ X0)
               grind)
            | exact resolve b5e28 b5e1147409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1147409
          have b5e1149320 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ y = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e1149187 X0
               have i₂ := b5e28 X0 x
               grind)
            | exact superpose b5e28 b5e1149187
            | (have j0 := b5e1149187 X0
               grind)
            | exact resolve b5e1149187 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1149187
          have b5e4369897 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e8412 (σ x) (σ y) x
               have i₂ := b5e215
               grind)
            | exact superpose b5e215 b5e8412
            | (have j0 := b5e8412 (σ x) x X0
               grind)
            | exact resolve b5e8412 b5e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4369898 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e8412 (σ y) (σ y) x
               have i₂ := b5e1251
               grind)
            | exact superpose b5e1251 b5e8412
            | (have j0 := b5e8412 (σ y) x X0
               grind)
            | exact resolve b5e8412 b5e1251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8412
          have b5e4369915 : ∀ X0 : G, y = (k y X0) ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e4369898 X0
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e4369898
            | (have j0 := b5e4369898 X0
               grind)
            | exact resolve b5e4369898 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4369898
          have b5e4369916 : ∀ X0 : G, x = (k x X0) ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e4369897 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e4369897
            | (have j0 := b5e4369897 X0
               grind)
            | exact resolve b5e4369897 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4369897
          have b5e4369918 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e4369915 X0
               have i₂ := b5e19 y X0
               grind)
            | exact superpose b5e19 b5e4369915
            | (have j0 := b5e4369915 X0
               grind)
            | exact resolve b5e4369915 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4369915
          have b5e4369919 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b5e4369916 X0
               have i₂ := b5e19 x X0
               grind)
            | exact superpose b5e19 b5e4369916
            | (have j0 := b5e4369916 X0
               grind)
            | exact resolve b5e4369916 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4369916
          have b5e4377147 : ∀ X0 : G, (M.op (σ y) X0) = (σ (k y (τ X0))) ∨ y = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e4369918 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e4369918
            | (have j0 := b5e4369918 (τ X0)
               grind)
            | exact resolve b5e4369918 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4377183 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ (k y X0)) X1) ∨ y = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 (σ y) (σ X0) X1
               have i₂ := b5e4369918 X0
               grind)
            | exact superpose b5e4369918 b5e40
            | (have j1 := b5e4369918 X0
               grind)
            | exact resolve b5e40 b5e4369918
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4369918
          have b5e4377201 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ y = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e4377147 X0
               have i₂ := b5e28 X0 y
               grind)
            | exact superpose b5e28 b5e4377147
            | (have j0 := b5e4377147 X0
               grind)
            | exact resolve b5e4377147 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e4377147
          have b5e4400939 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ (k x X0)) X1) ∨ x = (k x X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 (σ x) (σ X0) X1
               have i₂ := b5e4369919 X0
               grind)
            | exact superpose b5e4369919 b5e40
            | (have j1 := b5e4369919 X0
               grind)
            | exact resolve b5e40 b5e4369919
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4369919
          have b5e4403298 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ y) X0) ∨ y = (k y (τ X0)) ∨ y = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e1149320 X0
               have i₂ := b5e4377201 X0
               grind)
            | exact superpose b5e4377201 b5e1149320
            | (have j0 := b5e1149320 X0
               have j1 := b5e4377201 X0
               grind)
            | exact resolve b5e1149320 b5e4377201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1149320 b5e4377201
          have b5e4403324 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ y) X0) ∨ y = (k y (τ X0)) := by
            intro X0
            first
            | (have j0 := b5e4403298 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4403298
          have b5e4412931 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ y) (σ X0)) ∨ y = (k y (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e19 x X0
               have i₂ := b5e4403324 (σ X0)
               grind)
            | exact superpose b5e4403324 b5e19
            | (have j1 := b5e4403324 (σ X0)
               grind)
            | exact resolve b5e19 b5e4403324
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4403324
          have b5e4412955 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ y) (σ X0)) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e4412931 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e4412931
            | (have j0 := b5e4412931 X0
               grind)
            | exact resolve b5e4412931 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4412931
          have b5e4426312 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ (k x X0)) X1) ∨ y = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 (σ y) (σ X0) X1
               have i₂ := b5e4412955 X0
               grind)
            | exact superpose b5e4412955 b5e40
            | (have j1 := b5e4412955 X0
               grind)
            | exact resolve b5e40 b5e4412955
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4412955
          have b5e4457661 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op x X0)) X1) ∨ y = (k y X0) ∨ y = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e4377183 X0 X1
               have i₂ := b5e16410 X0
               grind)
            | exact superpose b5e16410 b5e4377183
            | (have j0 := b5e4377183 X0 X1
               have j1 := b5e16410 X0
               grind)
            | exact resolve b5e4377183 b5e16410
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16410 b5e4377183
          have b5e4457709 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op x X0)) X1) ∨ y = (k y X0) := by
            intro X0 X1
            first
            | (have j0 := b5e4457661 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4457661
          have b5e4466684 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ (M.op x X0)) X1) ∨ x = (k x X0) ∨ x = (k x X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e4400939 X0 X1
               have i₂ := b5e1029642 X0
               grind)
            | exact superpose b5e1029642 b5e4400939
            | (have j0 := b5e4400939 X0 X1
               have j1 := b5e1029642 X0
               grind)
            | exact resolve b5e4400939 b5e1029642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1029642
          have b5e4466725 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ (M.op x X0)) X1) ∨ x = (k x X0) := by
            intro X0 X1
            first
            | (have j0 := b5e4466684 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4466684
          have b5e4522295 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ y = (k y X1) ∨ x = (k x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e4457709 X1 X0
               have i₂ := b5e4466725 X1 X0
               grind)
            | exact superpose b5e4466725 b5e4457709
            | (have j0 := b5e4457709 X1 X1
               have j1 := b5e4466725 X1 X1
               grind)
            | exact resolve b5e4457709 b5e4466725
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4457709 b5e4466725
          have b5e5673410 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b5e1251
               have i₂ := b5e4522295 (σ y) X0
               grind)
            | exact superpose b5e4522295 b5e1251
            | (have j1 := b5e4522295 X0 X0
               grind)
            | exact resolve b5e1251 b5e4522295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4522295
          have b5e5673428 : ∀ X0 : G, y = (k y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have j0 := b5e5673410 X0
               grind)
            | (have r₁ := b5e5673410 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e5673410 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5673410
          have b5e5690507 : ∀ X0 : G, y = (M.op x X0) ∨ x = (k x X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b5e880066 X0
               have i₂ := b5e5673428 X0
               grind)
            | exact superpose b5e5673428 b5e880066
            | (have j0 := b5e880066 X0
               have j1 := b5e5673428 X0
               grind)
            | exact resolve b5e880066 b5e5673428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e880066 b5e5673428
          have b5e5690903 : ∀ X0 : G, x = (k x X0) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b5e5690507 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5690507
          have b5e5724072 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ y = (k y X1) ∨ y = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e4426312 X1 X0
               have i₂ := b5e5690903 X1
               grind)
            | exact superpose b5e5690903 b5e4426312
            | (have j0 := b5e4426312 X1 X1
               have j1 := b5e5690903 X1
               grind)
            | exact resolve b5e4426312 b5e5690903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4426312 b5e5690903
          have b5e5724413 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ y = (k y X1) := by
            intro X0 X1
            first
            | (have j0 := b5e5724072 X0 X1
               have j1 := b5e10447 X1
               grind)
            | (have r₁ := b5e5724072 X0 X0
               have r₂ := b5e10447 X0
               grind)
            | exact resolve b5e5724072 b5e10447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10447 b5e5724072
          have b5e6995239 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e1251
               have i₂ := b5e5724413 (σ y) X0
               grind)
            | exact superpose b5e5724413 b5e1251
            | (have j1 := b5e5724413 X0 X0
               grind)
            | exact resolve b5e1251 b5e5724413
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5724413
          have b5e6995392 : ∀ X0 : G, y = (k y X0) := by
            intro X0
            first
            | (have j0 := b5e6995239 X0
               grind)
            | (have r₁ := b5e6995239 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e6995239 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6995239
          have b5e7000212 : ∀ X0 : G, y = (M.op x X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e24568 X0
               have i₂ := b5e6995392 X0
               grind)
            | exact superpose b5e6995392 b5e24568
            | (have j0 := b5e24568 X0
               grind)
            | exact resolve b5e24568 b5e6995392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24568
          have b5e7000278 : ∀ X0 : G, y = (k (k x X0) (M.op x y)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e782771 X0
               have i₂ := b5e6995392 X0
               grind)
            | exact superpose b5e6995392 b5e782771
            | (have j0 := b5e782771 X0
               grind)
            | exact resolve b5e782771 b5e6995392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782771
          have b5e7000279 : ∀ X0 : G, y = (k (M.op x X0) (M.op x y)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e782773 X0
               have i₂ := b5e6995392 X0
               grind)
            | exact superpose b5e6995392 b5e782773
            | (have j0 := b5e782773 X0
               grind)
            | exact resolve b5e782773 b5e6995392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782773
          have b5e7000556 : ∀ X0 : G, (τ y) = (k (τ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e33 y X0
               have i₂ := b5e6995392 (σ X0)
               grind)
            | exact superpose b5e6995392 b5e33
            | exact resolve b5e33 b5e6995392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e7000782 : ∀ X0 : G, y = (k (M.op x X0) y) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e7000279 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e7000279
            | (have j0 := b5e7000279 X0
               grind)
            | exact resolve b5e7000279 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7000279
          have b5e7000783 : ∀ X0 : G, y = (k (k x X0) y) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e7000278 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e7000278
            | (have j0 := b5e7000278 X0
               grind)
            | exact resolve b5e7000278 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7000278
          have b5e7072923 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x X0) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e2369 X0
               have i₂ := b5e7000212 X0
               grind)
            | exact superpose b5e7000212 b5e2369
            | (have j1 := b5e7000212 X0
               grind)
            | exact resolve b5e2369 b5e7000212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2369
          have b5e7072993 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) ∨ y = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 x X0 X1
               have i₂ := b5e7000212 X0
               grind)
            | exact superpose b5e7000212 b5e40
            | (have j1 := b5e7000212 X0
               grind)
            | exact resolve b5e40 b5e7000212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7073044 : ∀ X0 : G, y ≠ X0 ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b5e7000212 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7000212
          have b5e7073055 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b5e7072923 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7072923
          have b5e7411836 : ∀ X0 : G, y = (M.op x X0) ∨ y = (M.op x (M.op x X0)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e7073055 (M.op x X0)
               have i₂ := b5e7000782 X0
               grind)
            | exact superpose b5e7000782 b5e7073055
            | (have j0 := b5e7073055 X0
               have j1 := b5e7000782 X0
               grind)
            | exact resolve b5e7073055 b5e7000782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7000782
          have b5e7411874 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e7411836 X0
               have j1 := b5e7073044 (M.op x X0)
               grind)
            | (have r₁ := b5e7411836 X0
               have r₂ := b5e7073044 (M.op x X0)
               grind)
            | (have r₁ := b5e7411836 X0
               have r₂ := b5e7073044 (M.op x (M.op x X0))
               grind)
            | (have r₁ := b5e7411836 y
               have r₂ := b5e7073044 (M.op x y)
               grind)
            | exact resolve b5e7411836 b5e7073044
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7411836
          have b5e7434141 : ∀ X0 : G, y = (k x X0) ∨ y = (M.op x (k x X0)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e7073055 (k x X0)
               have i₂ := b5e7000783 X0
               grind)
            | exact superpose b5e7000783 b5e7073055
            | (have j0 := b5e7073055 (k x X0)
               have j1 := b5e7000783 X0
               grind)
            | exact resolve b5e7073055 b5e7000783
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7000783 b5e7073055
          have b5e7434203 : ∀ X0 : G, y = (M.op x (k x X0)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e7434141 X0
               have j1 := b5e7073044 (k x X0)
               grind)
            | (have r₁ := b5e7434141 X0
               have r₂ := b5e7073044 (k x X0)
               grind)
            | (have r₁ := b5e7434141 X0
               have r₂ := b5e7073044 (M.op x (k x X0))
               grind)
            | (have r₁ := b5e7434141 y
               have r₂ := b5e7073044 (M.op x y)
               grind)
            | exact resolve b5e7434141 b5e7073044
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7073044 b5e7434141
          have b5e7490850 : (σ x) = (M.op x (σ y)) ∨ y = (M.op x (σ x)) := by
            first
            | (have i₁ := b5e215
               have i₂ := b5e7072993 (σ x) (σ y)
               grind)
            | exact superpose b5e7072993 b5e215
            | (have j1 := b5e7072993 (σ x) x
               grind)
            | exact resolve b5e215 b5e7072993
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e215 b5e7072993
          have b5e8537618 : y = (M.op x (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x (σ x)) := by
            first
            | (have i₁ := b5e7411874 (σ y)
               have i₂ := b5e7490850
               grind)
            | exact superpose b5e7490850 b5e7411874
            | exact resolve b5e7411874 b5e7490850
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7411874 b5e7490850
          have b5e8537632 : y = (M.op x (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e8537618
          have b5e8537638 : y = (M.op x (σ x)) := by
            first
            | (have r₁ := b5e8537632
               have r₂ := b5e216
               grind)
            | exact resolve b5e8537632 b5e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e216 b5e8537632
          have b5e8539824 : (k x (σ x)) = (k y (M.op x (k x (σ x)))) ∨ y = (σ x) := by
            first
            | (have i₁ := b5e782735 x (σ x)
               have i₂ := b5e8537638
               grind)
            | exact superpose b5e8537638 b5e782735
            | exact resolve b5e782735 b5e8537638
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e782735 b5e8537638
          have b5e8539858 : y = (k x (σ x)) ∨ y = (σ x) := by
            first
            | (have i₁ := b5e8539824
               have i₂ := b5e6995392 (M.op x (k x (σ x)))
               grind)
            | exact superpose b5e6995392 b5e8539824
            | exact resolve b5e8539824 b5e6995392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6995392 b5e8539824
          have b5e8553692 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y ∨ y = (σ x) := by
            intro X0
            first
            | (have i₁ := b5e4400939 (σ x) x
               have i₂ := b5e8539858
               grind)
            | exact superpose b5e8539858 b5e4400939
            | exact resolve b5e4400939 b5e8539858
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4400939 b5e8539858
          have b5e8553766 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ y = (σ x) := by
            intro X0
            first
            | (have j0 := b5e8553692 X0
               grind)
            | (have r₁ := b5e8553692 X0
               have r₂ := b5e1029444
               grind)
            | exact resolve b5e8553692 b5e1029444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1029444 b5e8553692
          have b5e9068646 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (σ x) := by
            first
            | (have i₁ := b5e1251
               have i₂ := b5e8553766 (σ y)
               grind)
            | exact superpose b5e8553766 b5e1251
            | exact resolve b5e1251 b5e8553766
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1251 b5e8553766
          have b5e9068692 : y = (σ x) := by
            first
            | (have r₁ := b5e9068646
               have r₂ := b5e24
               grind)
            | exact resolve b5e9068646 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9068646
          have b5e9077701 : x = (τ y) := by
            first
            | (have i₁ := b5e14 x
               have i₂ := b5e9068692
               grind)
            | exact superpose b5e9068692 b5e14
            | exact resolve b5e14 b5e9068692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9068692
          have b5e9092090 : ∀ X0 : G, x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b5e7000556 X0
               have i₂ := b5e9077701
               grind)
            | exact superpose b5e9077701 b5e7000556
            | exact resolve b5e7000556 b5e9077701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7000556 b5e9077701
          have b5e9115809 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e7434203 X0
               have i₂ := b5e9092090 X0
               grind)
            | exact superpose b5e9092090 b5e7434203
            | (have j0 := b5e7434203 X0
               grind)
            | exact resolve b5e7434203 b5e9092090
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7434203 b5e9092090
          have b5e9116231 : ∀ X0 : G, (M.op x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e9115809 X0
               grind)
            | (have r₁ := b5e9115809 X0
               have r₂ := b5e21
               grind)
            | exact resolve b5e9115809 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9115809
          have b5e9138448 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 x X0 X1
               have i₂ := b5e9116231 X0
               grind)
            | exact superpose b5e9116231 b5e40
            | exact resolve b5e40 b5e9116231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e9138709 : ∀ X0 X1 : G, (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e9138448 X0 X1
               have i₂ := b5e9116231 X1
               grind)
            | exact superpose b5e9116231 b5e9138448
            | exact resolve b5e9138448 b5e9116231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9116231 b5e9138448
          have b5e9170463 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e9138709 (σ x) (σ y)
               grind)
            | exact superpose b5e9138709 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e9138709 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e9138709
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9138709
          have b5e9170806 : False := by grind
          exact b5e9170806
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
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
        have b6e43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 (M.op X0 X0) X2
             have i₂ := b6e12 X0 X0 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
          intro X0
          grind
        have b6e45 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e43 X0 X1 x
             have i₂ := b6e12 X1 X0 x
             grind)
          | exact superpose b6e12 b6e43
          | exact resolve b6e43 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e47 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e45 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e45
          | exact resolve b6e45 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e90 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e106 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e90
             have r₂ := b6e20
             grind)
          | exact resolve b6e90 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e115 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e106
             have r₂ := b6e21
             grind)
          | exact resolve b6e106 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e198 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e47 (σ x)
             grind)
          | exact superpose b6e47 b6e19
          | exact resolve b6e19 b6e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e199 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e198
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e198
          | exact resolve b6e198 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e198
        have b6e208 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e199
             have i₂ := b6e115
             grind)
          | exact superpose b6e115 b6e199
          | exact resolve b6e199 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115 b6e199
        have b6e314 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e87 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e87
          | exact resolve b6e87 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e382 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e314
        have b6e409 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e382
             have r₂ := b6e208
             grind)
          | exact resolve b6e382 b6e208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e382
        have b6e453 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e409
             grind)
          | exact superpose b6e409 b6e13
          | exact resolve b6e13 b6e409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e465 : y = (k x x) := by
          first
          | (have i₁ := b6e453
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e453
          | exact resolve b6e453 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e453
        have b6e552 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e465
             grind)
          | exact superpose b6e465 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e465
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e465
        have b6e553 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e552
        have b6e555 : x = (M.op x x) := by
          first
          | (have r₁ := b6e553
             have r₂ := b6e20
             grind)
          | exact resolve b6e553 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e553
        have b6e613 : x = (k x x) := by
          first
          | (have i₁ := b6e44 x
             have i₂ := b6e555
             grind)
          | exact superpose b6e555 b6e44
          | exact resolve b6e44 b6e555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e555
        have b6e710 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e409
             have i₂ := b6e613
             grind)
          | exact superpose b6e613 b6e409
          | exact resolve b6e409 b6e613
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e409 b6e613
        have b6e721 : False := by grind
        exact b6e721
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b7e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X2) X3 (M.op X1 X1)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0) X2
               have i₂ := b7e13 X0 X0 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            grind
          have b7e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 X0 X1 x
               have i₂ := b7e13 X1 X0 x
               grind)
            | exact superpose b7e13 b7e31
            | exact resolve b7e31 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e34 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e30 X0 x X2 X3
               have i₂ := b7e13 X0 X3 x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e44 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 (M.op X0 X2) (M.op X1 X1)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e17
            | (have j0 := b7e17 X1 (M.op (M.op X0 X2) (M.op X0 X2))
               grind)
            | (have r₁ := b7e17 (M.op X0 X2) (M.op X0 X0)
               have r₂ := b7e13 X0 X0 X2
               grind)
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e44 X0 X1 X2
               have i₂ := b7e34 X0 X2 (M.op X0 X2)
               grind)
            | exact superpose b7e34 b7e44
            | (have j0 := b7e44 X0 X1 X2
               grind)
            | (have r₁ := b7e44 (M.op X0 X2) X0 X2
               have r₂ := b7e34 X0 X2 X0
               grind)
            | (have r₁ := b7e44 X0 (M.op X0 X2) X2
               have r₂ := b7e34 X0 X2 (M.op X0 X2)
               grind)
            | exact resolve b7e44 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
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
          have b7e52 : (k x y) = (τ (σ x)) := by
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
          have b7e53 : x = (k x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e52
            | exact resolve b7e52 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e66 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 X1
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e72 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e66 X0 X1 X2
               have i₂ := b7e33 X2 X0
               grind)
            | exact superpose b7e33 b7e66
            | (have j0 := b7e66 X0 X1 X2
               grind)
            | exact resolve b7e66 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e85 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
          have b7e86 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e21
               grind)
            | exact resolve b7e85 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e88 : x = (M.op x y) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e22
               grind)
            | exact resolve b7e86 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e90 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e34 (σ x) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e99 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e18 (M.op X0 X1) X2
               have i₂ := b7e34 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e34 b7e18
            | (have j0 := b7e18 (M.op X0 X1) X2
               grind)
            | exact resolve b7e18 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e100 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e33 (M.op X0 X1) X2
               have i₂ := b7e34 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e34 b7e33
            | exact resolve b7e33 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e102 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            grind
          have b7e103 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = X1 ∨ (M.op X0 X2) = (k (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 (M.op X0 X2) X1
               have i₂ := b7e34 X0 X2 X1
               grind)
            | exact superpose b7e34 b7e17
            | (have j0 := b7e17 (M.op X0 X2) X1
               grind)
            | exact resolve b7e17 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e108 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 (M.op X0 X2)) = X1 ∨ (M.op X0 X2) = (k (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e103 X0 X1 X2
               have i₂ := b7e34 X0 X2 (M.op X0 X2)
               grind)
            | exact superpose b7e34 b7e103
            | (have j0 := b7e103 X0 X1 X2
               grind)
            | exact resolve b7e103 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e110 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e99 X0 X1 X2
               have i₂ := b7e34 X0 X1 X2
               grind)
            | exact superpose b7e34 b7e99
            | (have j0 := b7e99 X0 X1 X2
               grind)
            | exact resolve b7e99 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e115 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e110 X0 X1 X2
               have i₂ := b7e34 X0 X1 X2
               grind)
            | exact superpose b7e34 b7e110
            | (have j0 := b7e110 X0 X1 X2
               grind)
            | exact resolve b7e110 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e117 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e88
               grind)
            | exact superpose b7e88 b7e26
            | exact resolve b7e26 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e118 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e88
               grind)
            | exact superpose b7e88 b7e22
            | exact resolve b7e22 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e122 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b7e126 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e27 X0 X1
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e127 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e122 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e122
            | exact resolve b7e122 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122
          have b7e134 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e28 X1 X0
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e161 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e32 X0
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e32 X0
               have i₂ := b7e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e18 b7e32
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e32 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e163 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 (M.op X0 x)
               have i₂ := b7e34 X0 x (M.op X0 x)
               grind)
            | exact superpose b7e34 b7e32
            | exact resolve b7e32 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e178 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
          have b7e180 : ∀ X0 : G, (M.op (σ x) X0) ≠ X0 ∨ (M.op (σ y) (σ y)) = X0 ∨ (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e17 (σ y) X0
               have i₂ := b7e90 X0
               grind)
            | exact superpose b7e90 b7e17
            | (have j0 := b7e17 (σ y) X0
               grind)
            | exact resolve b7e17 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e185 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ (M.op (σ x) X0) ≠ X0 ∨ (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e180 X0
               have i₂ := b7e90 (σ y)
               grind)
            | exact superpose b7e90 b7e180
            | (have j0 := b7e180 X0
               grind)
            | exact resolve b7e180 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e180
          have b7e187 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e178
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e178
            | exact resolve b7e178 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e178
          have b7e194 : ∀ X0 : G, (M.op (σ x) X0) ≠ X0 ∨ (σ y) = X0 ∨ (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e185 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e185
            | (have j0 := b7e185 X0
               grind)
            | (have r₁ := b7e185 (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e185 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e185
          have b7e195 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e187
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e187
            | exact resolve b7e187 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e187
          have b7e217 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e195
               grind)
            | exact superpose b7e195 b7e14
            | exact resolve b7e14 b7e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e195
          have b7e219 : y = (k y y) := by
            first
            | (have i₁ := b7e217
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e217
            | exact resolve b7e217 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e217
          have b7e225 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e219
               grind)
            | exact superpose b7e219 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e226 : y = (M.op y y) := by grind
          clear b7e225
          have b7e283 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op (M.op X2 X3) X0) = (k (M.op X2 X3) X0) ∨ (M.op (M.op X2 X3) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e34 X2 X3 X1
               have i₂ := b7e72 X0 (M.op X2 X3) X1
               grind)
            | (have i₁ := b7e34 X0 X2 X2
               have i₂ := b7e72 (M.op X0 X2) X1 X2
               grind)
            | exact superpose b7e72 b7e34
            | (have j1 := b7e72 X0 (M.op X2 X3) X2
               grind)
            | exact resolve b7e34 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e288 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e72 X1 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e291 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (k (M.op X2 X3) X0) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op (M.op X2 X3) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e283 X0 X1 X2 X3
               have i₂ := b7e34 X2 X3 X0
               grind)
            | exact superpose b7e34 b7e283
            | (have j0 := b7e283 X0 X1 X2 X3
               grind)
            | exact resolve b7e283 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e283
          have b7e315 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (k (M.op X2 X3) X0) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e291 X0 X1 X2 X3
               have i₂ := b7e34 X2 X3 X0
               grind)
            | exact superpose b7e34 b7e291
            | (have j0 := b7e291 X0 X1 X2 X3
               grind)
            | exact resolve b7e291 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e291
          have b7e359 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e126 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e126
            | exact resolve b7e126 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e428 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 X1
               have i₂ := b7e60 X0 X1
               grind)
            | exact superpose b7e60 b7e14
            | (have j1 := b7e60 X0 X1
               grind)
            | exact resolve b7e14 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e449 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e60 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e450 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e451 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e449 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e449
          have b7e548 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e47 X0 X0 X2
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e47 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b7e18 b7e47
            | (have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e47 X0 X0 X2
               have r₂ := b7e18 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b7e47 X0 X0 X2
               have r₂ := b7e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b7e47 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e567 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e47 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e571 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e548 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e548
          have b7e578 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e571 X0 X1 X2
               have j1 := b7e108 X1 X0 X2
               grind)
            | (have r₁ := b7e571 (M.op X0 X2) X0 X2
               have r₂ := b7e108 X0 (M.op X0 X2) X2
               grind)
            | (have r₁ := b7e571 (M.op X0 (M.op X1 (M.op X1 X2))) X1 X2
               have r₂ := b7e108 X0 (M.op X1 (M.op X1 X2)) X2
               grind)
            | (have r₁ := b7e571 X1 X0 X2
               have r₂ := b7e108 X0 X1 X2
               grind)
            | exact resolve b7e571 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108 b7e571
          have b7e604 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          have b7e619 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e604 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e604
            | exact resolve b7e604 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e604
          have b7e733 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X0) = (M.op X1 (M.op X1 X2)) ∨ (k X0 (M.op X1 (M.op X1 X2))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X0 (M.op X1 (M.op X1 X2))
               have i₂ := b7e100 X1 X2 X0
               grind)
            | exact superpose b7e100 b7e17
            | (have j0 := b7e17 X0 (M.op X1 (M.op X1 X2))
               grind)
            | (have r₁ := b7e17 X2 (M.op X2 (M.op X2 X1))
               have r₂ := b7e100 X2 X1 X2
               grind)
            | exact resolve b7e17 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e1265 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e451 (M.op X0 X0)
               have i₂ := b7e32 X0
               grind)
            | exact superpose b7e32 b7e451
            | (have j0 := b7e451 (M.op X0 X0)
               grind)
            | exact resolve b7e451 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1270 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e451 (τ X0)
               have i₂ := b7e27 X0 (τ X0)
               grind)
            | exact superpose b7e27 b7e451
            | (have j0 := b7e451 (τ X0)
               grind)
            | exact resolve b7e451 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27 b7e451
          have b7e1275 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b7e1265 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1265
          have b7e1278 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e1270 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1270
            | (have j0 := b7e1270 X0
               grind)
            | exact resolve b7e1270 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1270
          have b7e1282 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1278 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1278
            | (have j0 := b7e1278 X0
               grind)
            | exact resolve b7e1278 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1278
          have b7e1297 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e1282 (τ X0)
               have i₂ := b7e359 X0 X0
               grind)
            | exact superpose b7e359 b7e1282
            | (have j0 := b7e1282 (τ X0)
               grind)
            | exact resolve b7e1282 b7e359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1282
          have b7e1344 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e18 X0 X0
               have i₂ := b7e161 X0 X1
               grind)
            | exact superpose b7e161 b7e18
            | (have j0 := b7e18 X1 X0
               have j1 := b7e161 X0 X1
               grind)
            | exact resolve b7e18 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e161
          have b7e1357 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e1344 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1344
          have b7e1378 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e1357 X0 X1
               have j1 := b7e288 X1 X0
               grind)
            | (have r₁ := b7e1357 X1 X1
               have r₂ := b7e288 X0 X1
               grind)
            | (have r₁ := b7e1357 X1 X1
               have r₂ := b7e288 X0 X1
               grind)
            | exact resolve b7e1357 b7e288
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e288 b7e1357
          have b7e1435 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e1378 (σ X1) (σ X0)
               grind)
            | exact superpose b7e1378 b7e19
            | (have j1 := b7e1378 (σ X1) (σ X0)
               grind)
            | exact resolve b7e19 b7e1378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1438 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e134 X0 X1
               have i₂ := b7e1378 X1 (σ X0)
               grind)
            | exact superpose b7e1378 b7e134
            | (have j1 := b7e1378 X1 (σ X0)
               grind)
            | exact resolve b7e134 b7e1378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2302 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e567 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e567
            | exact resolve b7e567 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e567
          have b7e2356 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e2302
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2302
            | exact resolve b7e2302 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2302
          have b7e2366 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have r₁ := b7e2356
               have r₂ := b7e23
               grind)
            | exact resolve b7e2356 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2356
          have b7e2405 : (τ (σ y)) = (k y (τ (M.op (σ x) (σ x)))) := by
            first
            | (have i₁ := b7e134 y (M.op (σ x) (σ x))
               have i₂ := b7e2366
               grind)
            | exact superpose b7e2366 b7e134
            | exact resolve b7e134 b7e2366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2366
          have b7e2413 : y = (k y (τ (M.op (σ x) (σ x)))) := by
            first
            | (have i₁ := b7e2405
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e2405
            | exact resolve b7e2405 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2405
          have b7e2752 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e163 X0 X1
               have i₂ := b7e115 X0 X1 X2
               grind)
            | (have i₁ := b7e163 X0 X1
               have i₂ := b7e115 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b7e115 b7e163
            | (have j1 := b7e115 X1 X2 X0
               grind)
            | exact resolve b7e163 b7e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115 b7e163
          have b7e3474 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k (M.op X0 X2) X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e315 X1 X1 X0 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e315
          have b7e3559 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e1297 (M.op X0 X0)
               have i₂ := b7e32 X0
               grind)
            | exact superpose b7e32 b7e1297
            | (have j0 := b7e1297 (M.op X0 X0)
               grind)
            | exact resolve b7e1297 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e3566 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
            first
            | (have i₁ := b7e1297 y
               have i₂ := b7e219
               grind)
            | exact superpose b7e219 b7e1297
            | (have j0 := b7e1297 y
               grind)
            | exact resolve b7e1297 b7e219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219 b7e1297
          have b7e3573 : (τ y) = (M.op (τ y) (τ y)) := by grind
          clear b7e3566
          have b7e3577 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b7e3559 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3559
          have b7e4990 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ x) X0)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1438 y X0
               have i₂ := b7e90 X0
               grind)
            | exact superpose b7e90 b7e1438
            | (have j0 := b7e1438 x X0
               grind)
            | exact resolve b7e1438 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e5709 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e450 (τ X0) (τ X1)
               have i₂ := b7e359 X1 X0
               grind)
            | exact superpose b7e359 b7e450
            | (have j0 := b7e450 (τ X0) (τ X1)
               grind)
            | exact resolve b7e450 b7e359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e450
          have b7e5750 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e5709 X0 X1
               have i₂ := b7e15 (k X0 X1)
               grind)
            | exact superpose b7e15 b7e5709
            | (have j0 := b7e5709 X0 X1
               grind)
            | exact resolve b7e5709 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5709
          have b7e5757 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e5750 X0 X1
               have i₂ := b7e15 X1
               grind)
            | exact superpose b7e15 b7e5750
            | (have j0 := b7e5750 X0 X1
               grind)
            | exact resolve b7e5750 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5750
          have b7e5760 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e5757 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e5757
            | (have j0 := b7e5757 X0 X1
               grind)
            | exact resolve b7e5757 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5757
          have b7e5762 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e5760 X0 X1
               have i₂ := b7e15 X1
               grind)
            | exact superpose b7e15 b7e5760
            | (have j0 := b7e5760 X0 X1
               grind)
            | exact resolve b7e5760 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5760
          have b7e5763 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e5762 X0 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e5762
            | (have j0 := b7e5762 X0 X1
               grind)
            | exact resolve b7e5762 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5762
          have b7e5764 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e5763 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e5763
            | (have j0 := b7e5763 X0 X1
               grind)
            | exact resolve b7e5763 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5763
          have b7e5971 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e102 X1 X2
               have i₂ := b7e578 X0 X1 X2
               grind)
            | (have i₁ := b7e102 X0 X1
               have i₂ := b7e578 (M.op X0 (M.op X0 X1)) X1 X2
               grind)
            | exact superpose b7e578 b7e102
            | (have j1 := b7e578 X0 X1 X2
               grind)
            | exact resolve b7e102 b7e578
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102 b7e578
          have b7e6011 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e5971 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5971
          have b7e6603 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) X3) ∨ (M.op (M.op X0 X2) X3) = (k (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e6011 X0 (M.op X0 X2) X3
               have i₂ := b7e34 X0 X2 X3
               grind)
            | exact superpose b7e34 b7e6011
            | (have j0 := b7e6011 X3 X0 X1
               grind)
            | exact resolve b7e6011 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6619 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e6011 X0 x y
               have i₂ := b7e88
               grind)
            | exact superpose b7e88 b7e6011
            | (have j0 := b7e6011 X0 x x
               grind)
            | exact resolve b7e6011 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6620 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e6011 X0 y y
               have i₂ := b7e226
               grind)
            | exact superpose b7e226 b7e6011
            | (have j0 := b7e6011 X0 y x
               grind)
            | exact resolve b7e6011 b7e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6694 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k (M.op X0 X2) X3) ∨ (M.op X0 X1) = (k (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e6603 X0 X1 X2 X3
               have i₂ := b7e34 X0 X2 X3
               grind)
            | exact superpose b7e34 b7e6603
            | (have j0 := b7e6603 X0 X1 X2 X3
               grind)
            | exact resolve b7e6603 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6603
          have b7e7072 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have j0 := b7e6619 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7818 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ x) (σ X0)) ∨ (τ (M.op (σ y) (σ y))) = X0 ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e428 y x
               have i₂ := b7e90 (σ x)
               grind)
            | exact superpose b7e90 b7e428
            | (have j0 := b7e428 y X0
               grind)
            | exact resolve b7e428 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e428
          have b7e7944 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = X0 ∨ (σ (k y X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e7818 X0
               have i₂ := b7e90 (σ y)
               grind)
            | exact superpose b7e90 b7e7818
            | (have j0 := b7e7818 X0
               grind)
            | exact resolve b7e7818 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90 b7e7818
          have b7e7957 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k y X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e7944 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e7944
            | (have j0 := b7e7944 X0
               grind)
            | exact resolve b7e7944 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7944
          have b7e7961 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e7957 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e7957
            | (have j0 := b7e7957 X0
               grind)
            | exact resolve b7e7957 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7957
          have b7e13765 : ∀ X0 : G, (k y (τ X0)) = (k x (τ X0)) ∨ (M.op (σ x) X0) = X0 ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1438 x X0
               have i₂ := b7e4990 X0
               grind)
            | exact superpose b7e4990 b7e1438
            | (have j0 := b7e1438 x X0
               have j1 := b7e4990 X0
               grind)
            | exact resolve b7e1438 b7e4990
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1438 b7e4990
          have b7e13786 : ∀ X0 : G, (k y (τ X0)) = (k x (τ X0)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e13765 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13765
          have b7e14519 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ X0)) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e13786 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e13786
            | (have j0 := b7e13786 (σ X0)
               grind)
            | exact resolve b7e13786 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e14554 : ∀ X0 : G, (k (σ y) X0) = (σ (k x (τ X0))) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e28 X0 y
               have i₂ := b7e13786 X0
               grind)
            | exact superpose b7e13786 b7e28
            | (have j1 := b7e13786 X0
               grind)
            | exact resolve b7e28 b7e13786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e14585 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e14554 X0
               have i₂ := b7e28 X0 x
               grind)
            | exact superpose b7e28 b7e14554
            | (have j0 := b7e14554 X0
               grind)
            | exact resolve b7e14554 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14554
          have b7e16532 : y = (k y (τ (σ x))) ∨ (k x x) = (k y x) := by
            first
            | (have i₁ := b7e2413
               have i₂ := b7e14519 x
               grind)
            | exact superpose b7e14519 b7e2413
            | (have j1 := b7e14519 x
               grind)
            | exact resolve b7e2413 b7e14519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2413
          have b7e16563 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ X0) X1) ∨ (k x X0) = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 (σ x) (σ X0) X1
               have i₂ := b7e14519 X0
               grind)
            | exact superpose b7e14519 b7e34
            | (have j1 := b7e14519 X0
               grind)
            | exact resolve b7e34 b7e14519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e16615 : (k x x) = (k y x) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e16532
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e16532
            | exact resolve b7e16532 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e16532
          have b7e18134 : (k x x) = (M.op y x) ∨ y = (k x x) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e6620 x
               have i₂ := b7e16615
               grind)
            | exact superpose b7e16615 b7e6620
            | (have j0 := b7e6620 x
               grind)
            | exact resolve b7e6620 b7e16615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e18161 : x ≠ (k x x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e5764 y x
               have i₂ := b7e16615
               grind)
            | exact superpose b7e16615 b7e5764
            | (have j0 := b7e5764 y x
               grind)
            | exact resolve b7e5764 b7e16615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e18162 : y ≠ (k x x) ∨ y = (k y x) := by grind
          clear b7e16615
          have b7e18163 : x ≠ (k x x) ∨ x = (M.op y y) ∨ y = (k y x) := by
            first
            | (have j1 := b7e17 y x
               grind)
            | (have r₁ := b7e18161
               have r₂ := b7e17 x x
               grind)
            | (have r₁ := b7e18161
               have r₂ := b7e17 y x
               grind)
            | exact resolve b7e18161 b7e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e18161
          have b7e18168 : y = (k y x) ∨ (k x x) = (M.op y x) := by
            first
            | (have r₁ := b7e18134
               have r₂ := b7e18162
               grind)
            | exact resolve b7e18134 b7e18162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e18134 b7e18162
          have b7e18171 : x = y ∨ x ≠ (k x x) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e18163
               have i₂ := b7e226
               grind)
            | exact superpose b7e226 b7e18163
            | exact resolve b7e18163 b7e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e18163
          have b7e18175 : x ≠ (k x x) ∨ y = (k y x) := by
            first
            | (have r₁ := b7e18171
               have r₂ := b7e118
               grind)
            | exact resolve b7e18171 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e18171
          have b7e18999 : x ≠ (M.op x x) ∨ y = (k y x) ∨ x = (k x x) := by
            first
            | (have i₁ := b7e18175
               have i₂ := b7e6619 x
               grind)
            | exact superpose b7e6619 b7e18175
            | (have j1 := b7e6619 x
               grind)
            | (have r₁ := b7e18175
               have r₂ := b7e6619 x
               grind)
            | exact resolve b7e18175 b7e6619
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e19021 : x ≠ (M.op x x) ∨ y = (k y x) := by
            first
            | (have r₁ := b7e18999
               have r₂ := b7e18175
               grind)
            | exact resolve b7e18999 b7e18175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e18175 b7e18999
          have b7e21749 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e14585 (σ X0)
               grind)
            | exact superpose b7e14585 b7e19
            | (have j1 := b7e14585 (σ X0)
               grind)
            | exact resolve b7e19 b7e14585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14585
          have b7e21868 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e21749 X0
               have i₂ := b7e19 x X0
               grind)
            | exact superpose b7e19 b7e21749
            | (have j0 := b7e21749 X0
               grind)
            | exact resolve b7e21749 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21749
          have b7e40870 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ y) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e194 (σ X0)
               have i₂ := b7e14519 X0
               grind)
            | exact superpose b7e14519 b7e194
            | (have j0 := b7e194 (σ X0)
               have j1 := b7e14519 X0
               grind)
            | (have r₁ := b7e194 (σ X0)
               have r₂ := b7e14519 X0
               grind)
            | exact resolve b7e194 b7e14519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e194
          have b7e40945 : ∀ X0 : G, (σ X0) = (σ y) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b7e40870 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40870
          have b7e40972 : ∀ X0 : G, (σ y) = (σ (k y X0)) ∨ (σ X0) = (σ y) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e40945 X0
               have i₂ := b7e19 y X0
               grind)
            | exact superpose b7e19 b7e40945
            | (have j0 := b7e40945 X0
               grind)
            | exact resolve b7e40945 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40945
          have b7e41868 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e5764 X0 X0
               have i₂ := b7e2752 X0 X1 X2
               grind)
            | exact superpose b7e2752 b7e5764
            | (have j0 := b7e5764 X0 X0
               have j1 := b7e2752 X0 X1 X2
               grind)
            | (have r₁ := b7e5764 X0 X0
               have r₂ := b7e2752 X0 X1 X2
               grind)
            | exact resolve b7e5764 b7e2752
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2752
          have b7e41925 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e41868 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41868
          have b7e41926 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e41925 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41925
          have b7e42022 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e41926 X0 X1 X2
               have j1 := b7e3474 X1 X0 X2
               grind)
            | (have r₁ := b7e41926 X1 X1 X2
               have r₂ := b7e3474 X0 X1 X2
               grind)
            | (have r₁ := b7e41926 X1 X1 X2
               have r₂ := b7e3474 X0 X1 X2
               grind)
            | exact resolve b7e41926 b7e3474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3474 b7e41926
          have b7e49743 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ X0)))) = X0 ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e619 X0
               have i₂ := b7e16563 X0 (σ X0)
               grind)
            | (have i₁ := b7e619 x
               have i₂ := b7e16563 X0 (σ x)
               grind)
            | exact superpose b7e16563 b7e619
            | (have j1 := b7e16563 X0 x
               grind)
            | exact resolve b7e619 b7e16563
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e619
          have b7e66821 : (σ y) ≠ (σ (k y x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e7961 x
               grind)
            | exact superpose b7e7961 b7e23
            | (have j1 := b7e7961 x
               grind)
            | exact resolve b7e23 b7e7961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7961
          have b7e67032 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b7e66821
               have r₂ := b7e118
               grind)
            | exact resolve b7e66821 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66821
          have b7e67095 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k x x) = (M.op y x) := by
            first
            | (have i₁ := b7e67032
               have i₂ := b7e18168
               grind)
            | exact superpose b7e18168 b7e67032
            | exact resolve b7e67032 b7e18168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e18168 b7e67032
          have b7e67129 : (σ x) = (M.op (σ x) (σ x)) ∨ (k x x) = (M.op y x) := by grind
          clear b7e67095
          have b7e67673 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (k x x) = (M.op y x) := by
            first
            | (have i₁ := b7e3577 (σ x)
               have i₂ := b7e67129
               grind)
            | exact superpose b7e67129 b7e3577
            | exact resolve b7e3577 b7e67129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3577 b7e67129
          have b7e67738 : (k x x) = (M.op y x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e67673
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e67673
            | exact resolve b7e67673 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67673
          have b7e68113 : (M.op x x) = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e1378 x x
               have i₂ := b7e67738
               grind)
            | exact superpose b7e67738 b7e1378
            | (have j0 := b7e1378 x x
               grind)
            | exact resolve b7e1378 b7e67738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67738
          have b7e68124 : (M.op x x) = (M.op y x) ∨ x = (M.op x x) := by grind
          clear b7e68113
          have b7e70149 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x x) X0) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b7e34 y x X0
               have i₂ := b7e68124
               grind)
            | exact superpose b7e68124 b7e34
            | exact resolve b7e34 b7e68124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68124
          have b7e70215 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b7e70149 X0
               have i₂ := b7e34 x x X0
               grind)
            | exact superpose b7e34 b7e70149
            | exact resolve b7e70149 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70149
          have b7e74521 : y = (M.op x y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e226
               have i₂ := b7e70215 y
               grind)
            | exact superpose b7e70215 b7e226
            | exact resolve b7e226 b7e70215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e74523 : y = (k y (M.op x y)) ∨ x = (M.op x x) := by grind
          clear b7e70215
          have b7e74653 : y = (k y x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e74523
               have i₂ := b7e88
               grind)
            | exact superpose b7e88 b7e74523
            | exact resolve b7e74523 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e74523
          have b7e74655 : x = (M.op x x) := by
            first
            | (have r₁ := b7e74521
               have r₂ := b7e22
               grind)
            | exact resolve b7e74521 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74521
          have b7e74674 : y = (k y x) := by
            first
            | (have r₁ := b7e74653
               have r₂ := b7e19021
               grind)
            | exact resolve b7e74653 b7e19021
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19021 b7e74653
          have b7e75385 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e1275 x
               have i₂ := b7e74655
               grind)
            | exact superpose b7e74655 b7e1275
            | exact resolve b7e1275 b7e74655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1275
          have b7e76543 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e1378 x y
               have i₂ := b7e74674
               grind)
            | exact superpose b7e74674 b7e1378
            | (have j0 := b7e1378 x y
               grind)
            | exact resolve b7e1378 b7e74674
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74674
          have b7e77628 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e16563 X0 (σ x)
               have i₂ := b7e75385
               grind)
            | exact superpose b7e75385 b7e16563
            | (have j0 := b7e16563 X0 x
               grind)
            | exact resolve b7e16563 b7e75385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e16563
          have b7e77698 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e6011 X0 (σ x) (σ x)
               have i₂ := b7e75385
               grind)
            | exact superpose b7e75385 b7e6011
            | (have j0 := b7e6011 X0 (σ x) x
               grind)
            | exact resolve b7e6011 b7e75385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6011
          have b7e110500 : ∀ X0 : G, (k y (τ X0)) = (k x (τ X0)) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e77628 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e77628
            | (have j0 := b7e77628 (τ X0)
               grind)
            | exact resolve b7e77628 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77628
          have b7e122039 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b7e77698 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77698
          have b7e142525 : ∀ X0 : G, (k (σ y) X0) = (σ (k x (τ X0))) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e28 X0 y
               have i₂ := b7e110500 X0
               grind)
            | exact superpose b7e110500 b7e28
            | (have j1 := b7e110500 X0
               grind)
            | exact resolve b7e28 b7e110500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110500
          have b7e142605 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e142525 X0
               have i₂ := b7e28 X0 x
               grind)
            | exact superpose b7e28 b7e142525
            | (have j0 := b7e142525 X0
               grind)
            | exact resolve b7e142525 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e142525
          have b7e158205 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k y X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e142605 (σ X0)
               grind)
            | exact superpose b7e142605 b7e19
            | (have j1 := b7e142605 (σ X0)
               grind)
            | exact resolve b7e19 b7e142605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142605
          have b7e158491 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e158205 X0
               have i₂ := b7e19 x X0
               grind)
            | exact superpose b7e19 b7e158205
            | (have j0 := b7e158205 X0
               grind)
            | exact resolve b7e158205 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e158205
          have b7e203469 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e733 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e733
          have b7e216088 : ∀ X0 : G, (σ X0) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e122039 (σ X0)
               have i₂ := b7e21868 X0
               grind)
            | exact superpose b7e21868 b7e122039
            | (have j0 := b7e122039 (σ X0)
               have j1 := b7e21868 X0
               grind)
            | (have r₁ := b7e122039 (σ x)
               have r₂ := b7e21868 x
               grind)
            | exact resolve b7e122039 b7e21868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122039
          have b7e216147 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e17 (σ x) (σ X0)
               have i₂ := b7e21868 X0
               grind)
            | exact superpose b7e21868 b7e17
            | (have j0 := b7e17 (σ x) (σ X0)
               have j1 := b7e21868 X0
               grind)
            | (have r₁ := b7e17 (σ x) (σ X0)
               have r₂ := b7e21868 X0
               grind)
            | exact resolve b7e17 b7e21868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21868
          have b7e216274 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have j0 := b7e216147 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216147
          have b7e216291 : ∀ X0 : G, (σ X0) = (σ x) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e216274 X0
               have i₂ := b7e75385
               grind)
            | exact superpose b7e75385 b7e216274
            | (have j0 := b7e216274 X0
               grind)
            | exact resolve b7e216274 b7e75385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75385 b7e216274
          have b7e216302 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ (σ X0) ≠ (σ x) ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e216088 X0
               have i₂ := b7e19 x X0
               grind)
            | exact superpose b7e19 b7e216088
            | (have j0 := b7e216088 X0
               grind)
            | exact resolve b7e216088 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216088
          have b7e216328 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ (σ X0) = (σ x) ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e216291 X0
               have i₂ := b7e19 x X0
               grind)
            | exact superpose b7e19 b7e216291
            | (have j0 := b7e216291 X0
               grind)
            | exact resolve b7e216291 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216291
          have b7e216333 : ∀ X0 : G, (σ (k x X0)) = (σ (k y X0)) ∨ (σ x) = (σ (k x X0)) := by
            intro X0
            first
            | (have j0 := b7e216328 X0
               have j1 := b7e216302 X0
               grind)
            | (have r₁ := b7e216328 X0
               have r₂ := b7e216302 (k x X0)
               grind)
            | (have r₁ := b7e216328 X0
               have r₂ := b7e216302 X0
               grind)
            | (have r₁ := b7e216328 x
               have r₂ := b7e216302 x
               grind)
            | exact resolve b7e216328 b7e216302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216302 b7e216328
          have b7e216732 : ∀ X0 : G, (k y X0) = (τ (σ (k x X0))) ∨ (σ x) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b7e14 (k y X0)
               have i₂ := b7e216333 X0
               grind)
            | exact superpose b7e216333 b7e14
            | (have j1 := b7e216333 X0
               grind)
            | exact resolve b7e14 b7e216333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216333
          have b7e216976 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e216732 X0
               have i₂ := b7e14 (k x X0)
               grind)
            | exact superpose b7e14 b7e216732
            | (have j0 := b7e216732 X0
               grind)
            | exact resolve b7e216732 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216732
          have b7e219122 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ (M.op x X0) = (k y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e216976 X0
               have i₂ := b7e6619 X0
               grind)
            | exact superpose b7e6619 b7e216976
            | (have j1 := b7e6619 X0
               grind)
            | exact resolve b7e216976 b7e6619
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6619 b7e216976
          have b7e278594 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (k x X0) = (k y X0) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e49743 X0
               have i₂ := b7e14519 X0
               grind)
            | exact superpose b7e14519 b7e49743
            | (have j0 := b7e49743 X0
               have j1 := b7e14519 X0
               grind)
            | exact resolve b7e49743 b7e14519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49743
          have b7e279045 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b7e278594 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e278594
          have b7e279153 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e279045 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e279045
            | (have j0 := b7e279045 X0
               grind)
            | exact resolve b7e279045 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e279045
          have b7e280646 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e5764 X0 X0
               have i₂ := b7e279153 X0
               grind)
            | exact superpose b7e279153 b7e5764
            | (have j0 := b7e5764 X0 X0
               have j1 := b7e279153 X0
               grind)
            | (have r₁ := b7e5764 X0 X0
               have r₂ := b7e279153 X0
               grind)
            | exact resolve b7e5764 b7e279153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5764 b7e279153
          have b7e281022 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b7e280646 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e280646
          have b7e281023 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b7e281022 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e281022
          have b7e282824 : ∀ X0 : G, (k x X0) = (M.op y X0) ∨ (M.op X0 X0) = X0 ∨ y = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e6620 X0
               have i₂ := b7e281023 X0
               grind)
            | exact superpose b7e281023 b7e6620
            | (have j1 := b7e281023 X0
               grind)
            | exact resolve b7e6620 b7e281023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e281023
          have b7e613990 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e1435 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1435
          have b7e617077 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e613990 (τ X0) (τ X1)
               have i₂ := b7e359 X1 X0
               grind)
            | exact superpose b7e359 b7e613990
            | (have j0 := b7e613990 (τ X0) (τ X1)
               grind)
            | exact resolve b7e613990 b7e359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e613990
          have b7e617362 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e617077 X0 X1
               have i₂ := b7e15 (k X0 X1)
               grind)
            | exact superpose b7e15 b7e617077
            | (have j0 := b7e617077 X0 X1
               grind)
            | exact resolve b7e617077 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e617077
          have b7e617394 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e617362 X0 X1
               have i₂ := b7e15 X1
               grind)
            | exact superpose b7e15 b7e617362
            | (have j0 := b7e617362 X0 X1
               grind)
            | exact resolve b7e617362 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e617362
          have b7e617410 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e617394 X0 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e617394
            | (have j0 := b7e617394 X0 X1
               grind)
            | exact resolve b7e617394 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e617394
          have b7e617422 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e617410 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e617410
            | (have j0 := b7e617410 X0 X1
               grind)
            | exact resolve b7e617410 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e617410
          have b7e741284 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e6694 X0 X1 X2 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e741285 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e6694 X0 X1 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6694
          have b7e745279 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e741284 (σ x) (σ y) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e741284
            | exact resolve b7e741284 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e769297 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e745279 (σ X0)
               have i₂ := b7e14519 X0
               grind)
            | exact superpose b7e14519 b7e745279
            | (have j0 := b7e745279 (σ X0)
               have j1 := b7e14519 X0
               grind)
            | (have r₁ := b7e745279 (σ y)
               have r₂ := b7e14519 y
               grind)
            | exact resolve b7e745279 b7e14519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14519 b7e745279
          have b7e769354 : ∀ X0 : G, (σ y) = (σ (k y X0)) ∨ (σ X0) ≠ (σ y) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e769297 X0
               have i₂ := b7e19 y X0
               grind)
            | exact superpose b7e19 b7e769297
            | (have j0 := b7e769297 X0
               grind)
            | exact resolve b7e769297 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e769297
          have b7e769364 : ∀ X0 : G, (σ y) = (σ (k y X0)) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b7e769354 X0
               have j1 := b7e40972 X0
               grind)
            | (have r₁ := b7e769354 (k y X0)
               have r₂ := b7e40972 X0
               grind)
            | (have r₁ := b7e769354 X0
               have r₂ := b7e40972 X0
               grind)
            | (have r₁ := b7e769354 y
               have r₂ := b7e40972 y
               grind)
            | exact resolve b7e769354 b7e40972
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40972 b7e769354
          have b7e777986 : ∀ X0 : G, (τ (σ y)) = (k y X0) ∨ (k x X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e14 (k y X0)
               have i₂ := b7e769364 X0
               grind)
            | exact superpose b7e769364 b7e14
            | (have j1 := b7e769364 X0
               grind)
            | exact resolve b7e14 b7e769364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e769364
          have b7e778090 : ∀ X0 : G, (k x X0) = (k y X0) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e777986 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e777986
            | (have j0 := b7e777986 X0
               grind)
            | exact resolve b7e777986 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e777986
          have b7e780194 : ∀ X0 : G, (k x X0) = (M.op y X0) ∨ y = (k x X0) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e6620 X0
               have i₂ := b7e778090 X0
               grind)
            | exact superpose b7e778090 b7e6620
            | (have j0 := b7e6620 X0
               have j1 := b7e778090 X0
               grind)
            | exact resolve b7e6620 b7e778090
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6620
          have b7e780412 : ∀ X0 : G, y ≠ (k x X0) ∨ y = (k y X0) := by
            intro X0
            first
            | (have j0 := b7e778090 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e778090
          have b7e780469 : ∀ X0 : G, y = (k y X0) ∨ (k x X0) = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b7e780194 X0
               have j1 := b7e780412 X0
               grind)
            | (have r₁ := b7e780194 X0
               have r₂ := b7e780412 X0
               grind)
            | exact resolve b7e780194 b7e780412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e780194 b7e780412
          have b7e788698 : ∀ X0 : G, (τ y) = (k (τ y) X0) ∨ (M.op y (σ X0)) = (k x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e126 y X0
               have i₂ := b7e780469 (σ X0)
               grind)
            | exact superpose b7e780469 b7e126
            | (have j1 := b7e780469 (σ X0)
               grind)
            | exact resolve b7e126 b7e780469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126
          have b7e901930 : ∀ X0 : G, (τ y) = (τ (k y X0)) ∨ (k x (σ (τ X0))) = (M.op y (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e359 X0 y
               have i₂ := b7e788698 (τ X0)
               grind)
            | exact superpose b7e788698 b7e359
            | (have j1 := b7e788698 (τ X0)
               grind)
            | exact resolve b7e359 b7e788698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e359 b7e788698
          have b7e901975 : ∀ X0 : G, (τ y) = (τ (k y X0)) ∨ (k x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e901930 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e901930
            | (have j0 := b7e901930 X0
               grind)
            | exact resolve b7e901930 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e901930
          have b7e906092 : ∀ X0 : G, (k y X0) = (k (k y X0) (σ (M.op (τ y) (τ y)))) ∨ (k x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e127 (k y X0)
               have i₂ := b7e901975 X0
               grind)
            | exact superpose b7e901975 b7e127
            | (have j1 := b7e901975 X0
               grind)
            | exact resolve b7e127 b7e901975
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127 b7e901975
          have b7e906118 : ∀ X0 : G, (k y X0) = (k (k y X0) (σ (τ y))) ∨ (k x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e906092 X0
               have i₂ := b7e3573
               grind)
            | exact superpose b7e3573 b7e906092
            | (have j0 := b7e906092 X0
               grind)
            | exact resolve b7e906092 b7e3573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3573 b7e906092
          have b7e906130 : ∀ X0 : G, (k y X0) = (k (k y X0) y) ∨ (k x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e906118 X0
               have i₂ := b7e15 y
               grind)
            | exact superpose b7e15 b7e906118
            | (have j0 := b7e906118 X0
               grind)
            | exact resolve b7e906118 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e906118
          have b7e939142 : ∀ X0 : G, y ≠ (k y X0) ∨ y = (M.op (k y X0) y) ∨ (k x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e617422 (k y X0) y
               have i₂ := b7e906130 X0
               grind)
            | exact superpose b7e906130 b7e617422
            | (have j0 := b7e617422 (k y X0) y
               have j1 := b7e906130 X0
               grind)
            | exact resolve b7e617422 b7e906130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e906130
          have b7e939157 : ∀ X0 : G, y = (M.op (k y X0) y) ∨ (k x X0) = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b7e939142 X0
               have j1 := b7e780469 X0
               grind)
            | (have r₁ := b7e939142 X0
               have r₂ := b7e780469 X0
               grind)
            | exact resolve b7e939142 b7e780469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e780469 b7e939142
          have b7e9864306 : ∀ X0 : G, (τ (σ x)) = (M.op x X0) ∨ (M.op x X0) = (k y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e14 (M.op x X0)
               have i₂ := b7e219122 X0
               grind)
            | exact superpose b7e219122 b7e14
            | (have j1 := b7e219122 X0
               grind)
            | exact resolve b7e14 b7e219122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219122
          have b7e9864307 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x X0) = (k y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e9864306 X0
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e9864306
            | (have j0 := b7e9864306 X0
               grind)
            | exact resolve b7e9864306 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9864306
          have b7e9864308 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have j0 := b7e9864307 X0
               have j1 := b7e7072 X0
               grind)
            | (have r₁ := b7e9864307 X0
               have r₂ := b7e7072 X0
               grind)
            | exact resolve b7e9864307 b7e7072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9864307
          have b7e9868525 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ (k x X0) = (M.op y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e939157 X0
               have i₂ := b7e9864308 X0
               grind)
            | exact superpose b7e9864308 b7e939157
            | (have j0 := b7e939157 X0
               have j1 := b7e9864308 X0
               grind)
            | exact resolve b7e939157 b7e9864308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e939157 b7e9864308
          have b7e9868622 : ∀ X0 : G, y = (M.op x y) ∨ (k x X0) = (M.op y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e9868525 X0
               have i₂ := b7e34 x X0 y
               grind)
            | exact superpose b7e34 b7e9868525
            | (have j0 := b7e9868525 X0
               grind)
            | exact resolve b7e9868525 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9868525
          have b7e9868631 : ∀ X0 : G, (k x X0) = (M.op y X0) ∨ x = (k x X0) := by
            intro X0
            first
            | (have j0 := b7e9868622 X0
               grind)
            | (have r₁ := b7e9868622 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e9868622 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9868622
          have b7e9903347 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (M.op x X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e9868631 X0
               have i₂ := b7e1378 X0 x
               grind)
            | exact superpose b7e1378 b7e9868631
            | (have j1 := b7e1378 X0 x
               grind)
            | exact resolve b7e9868631 b7e1378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1378 b7e9868631
          have b7e10717215 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op x X0) X1) ∨ x = (M.op x X0) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e34 y X0 X1
               have i₂ := b7e9903347 X0
               grind)
            | exact superpose b7e9903347 b7e34
            | (have j1 := b7e9903347 X0
               grind)
            | exact resolve b7e34 b7e9903347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9903347
          have b7e10717230 : ∀ X0 X1 : G, (M.op x X1) = (M.op y X1) ∨ x = (M.op x X0) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e10717215 X0 X1
               have i₂ := b7e34 x X0 X1
               grind)
            | exact superpose b7e34 b7e10717215
            | (have j0 := b7e10717215 X0 X1
               grind)
            | exact resolve b7e10717215 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10717215
          have b7e10848382 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e226
               have i₂ := b7e10717230 X0 y
               grind)
            | exact superpose b7e10717230 b7e226
            | (have j1 := b7e10717230 X0 x
               grind)
            | exact resolve b7e226 b7e10717230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10717230
          have b7e10848411 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e10848382 X0
               grind)
            | (have r₁ := b7e10848382 X0
               have r₂ := b7e22
               grind)
            | (have r₁ := b7e10848382 y
               have r₂ := b7e22
               grind)
            | exact resolve b7e10848382 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10848382
          have b7e10863095 : ∀ X0 : G, x ≠ X0 ∨ x = (k x X0) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e7072 X0
               have i₂ := b7e10848411 X0
               grind)
            | exact superpose b7e10848411 b7e7072
            | (have j0 := b7e7072 X0
               have j1 := b7e10848411 X0
               grind)
            | (have r₁ := b7e7072 X0
               have r₂ := b7e10848411 X0
               grind)
            | (have r₁ := b7e7072 x
               have r₂ := b7e10848411 x
               grind)
            | exact resolve b7e7072 b7e10848411
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e10863130 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x x) = X0 ∨ x = (k x X0) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e17 x X0
               have i₂ := b7e10848411 X0
               grind)
            | exact superpose b7e10848411 b7e17
            | (have j0 := b7e17 x X0
               have j1 := b7e10848411 X0
               grind)
            | (have r₁ := b7e17 x x
               have r₂ := b7e10848411 x
               grind)
            | (have r₁ := b7e17 x X0
               have r₂ := b7e10848411 X0
               grind)
            | exact resolve b7e17 b7e10848411
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10848411
          have b7e10863192 : ∀ X0 : G, (M.op x x) = X0 ∨ x = (k x X0) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b7e10863130 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10863130
          have b7e10863226 : ∀ X0 : G, (M.op x x) = X0 ∨ x = (k x X0) := by
            intro X0
            first
            | (have j0 := b7e10863192 X0
               have j1 := b7e7072 X0
               grind)
            | (have r₁ := b7e10863192 x
               have r₂ := b7e7072 x
               grind)
            | (have r₁ := b7e10863192 X0
               have r₂ := b7e7072 X0
               grind)
            | exact resolve b7e10863192 b7e7072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10863192
          have b7e10863239 : ∀ X0 : G, x ≠ X0 ∨ x = (k x X0) := by
            intro X0
            first
            | (have j0 := b7e10863095 X0
               have j1 := b7e7072 X0
               grind)
            | (have r₁ := b7e10863095 (k x X0)
               have r₂ := b7e7072 X0
               grind)
            | (have r₁ := b7e10863095 X0
               have r₂ := b7e7072 X0
               grind)
            | exact resolve b7e10863095 b7e7072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7072 b7e10863095
          have b7e10863251 : ∀ X0 : G, x = X0 ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e10863226 X0
               have i₂ := b7e74655
               grind)
            | exact superpose b7e74655 b7e10863226
            | (have j0 := b7e10863226 X0
               grind)
            | exact resolve b7e10863226 b7e74655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74655 b7e10863226
          have b7e10863256 : ∀ X0 : G, x = (k x X0) := by
            intro X0
            first
            | (have j0 := b7e10863251 (k x X0)
               have j1 := b7e10863239 X0
               grind)
            | (have r₁ := b7e10863251 X0
               have r₂ := b7e10863239 X0
               grind)
            | (have r₁ := b7e10863251 x
               have r₂ := b7e10863239 x
               grind)
            | (have r₁ := b7e10863251 X0
               have r₂ := b7e10863239 (k x X0)
               grind)
            | exact resolve b7e10863251 b7e10863239
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10863239 b7e10863251
          have b7e10869041 : ∀ X0 : G, x = (M.op y X0) ∨ (M.op X0 X0) = X0 ∨ x = y := by
            intro X0
            first
            | (have i₁ := b7e282824 X0
               have i₂ := b7e10863256 X0
               grind)
            | exact superpose b7e10863256 b7e282824
            | (have j0 := b7e282824 X0
               grind)
            | exact resolve b7e282824 b7e10863256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e282824
          have b7e10869533 : ∀ X0 : G, x = (M.op y X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e10869041 X0
               grind)
            | (have r₁ := b7e10869041 X0
               have r₂ := b7e118
               grind)
            | exact resolve b7e10869041 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10869041
          have b7e11239293 : ∀ X0 X1 : G, (M.op x X1) = (M.op y X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e34 y X0 X1
               have i₂ := b7e10869533 X0
               grind)
            | exact superpose b7e10869533 b7e34
            | (have j1 := b7e10869533 X0
               grind)
            | exact resolve b7e34 b7e10869533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10869533
          have b7e12474419 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e226
               have i₂ := b7e11239293 X0 y
               grind)
            | exact superpose b7e11239293 b7e226
            | (have j1 := b7e11239293 X0 x
               grind)
            | exact resolve b7e226 b7e11239293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e226 b7e11239293
          have b7e12474572 : ∀ X0 : G, (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e12474419 X0
               grind)
            | (have r₁ := b7e12474419 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e12474419 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12474419
          have b7e12499168 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e741284 X0 X0 x
               have i₂ := b7e12474572 X0
               grind)
            | exact superpose b7e12474572 b7e741284
            | exact resolve b7e741284 b7e12474572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e741284
          have b7e12499170 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e741285 X0 X0 x
               have i₂ := b7e12474572 X0
               grind)
            | exact superpose b7e12474572 b7e741285
            | exact resolve b7e741285 b7e12474572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e741285
          have b7e12499249 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 X1 (M.op X0 X1)
               have i₂ := b7e12474572 (M.op X0 X1)
               grind)
            | exact superpose b7e12474572 b7e34
            | exact resolve b7e34 b7e12474572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e12547827 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e203469 X0 X1
               have i₂ := b7e12499249 X0 X1
               grind)
            | exact superpose b7e12499249 b7e203469
            | exact resolve b7e203469 b7e12499249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e203469
          have b7e12547963 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e12547827 X0 X1
               have i₂ := b7e12474572 X0
               grind)
            | exact superpose b7e12474572 b7e12547827
            | (have j0 := b7e12547827 X0 X1
               grind)
            | exact resolve b7e12547827 b7e12474572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12547827
          have b7e12622025 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e12499168 X0 (M.op X0 X1)
               have i₂ := b7e12499249 X0 X1
               grind)
            | exact superpose b7e12499249 b7e12499168
            | (have j0 := b7e12499168 X0 X1
               grind)
            | exact resolve b7e12499168 b7e12499249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12499168 b7e12499249
          have b7e12622133 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e12622025 X0 X1
               have j1 := b7e12547963 X0 X1
               grind)
            | (have r₁ := b7e12622025 X0 X1
               have r₂ := b7e12547963 X0 X1
               grind)
            | exact resolve b7e12622025 b7e12547963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12547963 b7e12622025
          have b7e12649387 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e134 X0 (M.op (σ X0) X1)
               have i₂ := b7e12622133 (σ X0) X1
               grind)
            | exact superpose b7e12622133 b7e134
            | exact resolve b7e134 b7e12622133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134
          have b7e12649542 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e12649387 X0 X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e12649387
            | exact resolve b7e12649387 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12649387
          have b7e12695101 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e12649542 X0 (σ x)
               have i₂ := b7e158491 X0
               grind)
            | exact superpose b7e158491 b7e12649542
            | (have j1 := b7e158491 X0
               grind)
            | exact resolve b7e12649542 b7e158491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e158491 b7e12649542
          have b7e12695294 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ (k x X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e12695101 X0
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e12695101
            | (have j0 := b7e12695101 X0
               grind)
            | exact resolve b7e12695101 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12695101
          have b7e12695312 : ∀ X0 : G, (σ x) = (σ (k y X0)) ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e12695294 X0
               have i₂ := b7e10863256 X0
               grind)
            | exact superpose b7e10863256 b7e12695294
            | (have j0 := b7e12695294 X0
               grind)
            | exact resolve b7e12695294 b7e10863256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12695294
          have b7e13646085 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op y X0) = (k (M.op y X0) x) := by
            intro X0
            first
            | (have i₁ := b7e12695312 (M.op y X0)
               have i₂ := b7e12622133 y X0
               grind)
            | exact superpose b7e12622133 b7e12695312
            | (have j0 := b7e12695312 (M.op y X0)
               grind)
            | exact resolve b7e12695312 b7e12622133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12622133 b7e12695312
          have b7e13646106 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) x) := by
            intro X0
            first
            | (have j0 := b7e13646085 X0
               grind)
            | (have r₁ := b7e13646085 X0
               have r₂ := b7e117
               grind)
            | exact resolve b7e13646085 b7e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117 b7e13646085
          have b7e13646191 : ∀ X0 : G, (M.op y X0) = (M.op y x) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e42022 x y X0
               have i₂ := b7e13646106 X0
               grind)
            | exact superpose b7e13646106 b7e42022
            | (have j0 := b7e42022 x y x
               grind)
            | exact resolve b7e42022 b7e13646106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42022
          have b7e13646196 : ∀ X0 : G, x ≠ (M.op y X0) ∨ x = (M.op (M.op y X0) x) := by
            intro X0
            first
            | (have i₁ := b7e617422 (M.op y X0) x
               have i₂ := b7e13646106 X0
               grind)
            | exact superpose b7e13646106 b7e617422
            | (have j0 := b7e617422 (M.op y X0) x
               grind)
            | exact resolve b7e617422 b7e13646106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e617422 b7e13646106
          have b7e13646198 : ∀ X0 : G, x ≠ (M.op y X0) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e13646196 X0
               have i₂ := b7e34 y X0 x
               grind)
            | exact superpose b7e34 b7e13646196
            | (have j0 := b7e13646196 X0
               grind)
            | exact resolve b7e13646196 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13646196
          have b7e13646758 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op y X0) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e76543
               have i₂ := b7e13646191 x
               grind)
            | (have i₁ := b7e76543
               have i₂ := b7e13646191 X0
               grind)
            | exact superpose b7e13646191 b7e76543
            | exact resolve b7e76543 b7e13646191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76543 b7e13646191
          have b7e13646816 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have j0 := b7e13646758 X0
               grind)
            | (have r₁ := b7e13646758 X0
               have r₂ := b7e13646198 X0
               grind)
            | (have r₁ := b7e13646758 X0
               have r₂ := b7e13646198 x
               grind)
            | exact resolve b7e13646758 b7e13646198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13646198 b7e13646758
          have b7e13647057 : ∀ X0 X1 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 y x X0
               have i₂ := b7e13646816 X1
               grind)
            | exact superpose b7e13646816 b7e34
            | (have j1 := b7e13646816 X1
               grind)
            | exact resolve b7e34 b7e13646816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e13646816
          have b7e13647822 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e12474572 y
               have i₂ := b7e13647057 y X0
               grind)
            | exact superpose b7e13647057 b7e12474572
            | (have j1 := b7e13647057 X0 X0
               grind)
            | exact resolve b7e12474572 b7e13647057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13647057
          have b7e13647924 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b7e13647822 X0
               grind)
            | (have r₁ := b7e13647822 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e13647822 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13647822
          have b7e13648341 : ∀ X0 : G, y ≠ y ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e12499170 y X0
               have i₂ := b7e13647924 X0
               grind)
            | exact superpose b7e13647924 b7e12499170
            | (have r₁ := b7e12499170 y X0
               have r₂ := b7e13647924 X0
               grind)
            | exact resolve b7e12499170 b7e13647924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12499170 b7e13647924
          have b7e13648464 : ∀ X0 : G, y = (k y X0) := by
            intro X0
            first
            | (have j0 := b7e13648341 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13648341
          have b7e13648935 : ∀ X0 : G, y = (k x (τ X0)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13786 X0
               have i₂ := b7e13648464 (τ X0)
               grind)
            | exact superpose b7e13648464 b7e13786
            | (have j0 := b7e13786 X0
               grind)
            | exact resolve b7e13786 b7e13648464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13786 b7e13648464
          have b7e13649296 : ∀ X0 : G, x = y ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13648935 X0
               have i₂ := b7e10863256 (τ X0)
               grind)
            | exact superpose b7e10863256 b7e13648935
            | (have j0 := b7e13648935 X0
               grind)
            | exact resolve b7e13648935 b7e10863256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10863256 b7e13648935
          have b7e13649342 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e13649296 X0
               grind)
            | (have r₁ := b7e13649296 X0
               have r₂ := b7e118
               grind)
            | exact resolve b7e13649296 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118 b7e13649296
          have b7e13653001 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) X1 X0
               have i₂ := b7e13649342 X0
               grind)
            | exact superpose b7e13649342 b7e13
            | exact resolve b7e13 b7e13649342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e13653115 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13653001 X0 X1
               have i₂ := b7e13649342 X1
               grind)
            | exact superpose b7e13649342 b7e13653001
            | exact resolve b7e13653001 b7e13649342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13649342 b7e13653001
          have b7e13653154 : ∀ X0 X1 : G, (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13653115 X0 X1
               have i₂ := b7e12474572 X1
               grind)
            | exact superpose b7e12474572 b7e13653115
            | exact resolve b7e13653115 b7e12474572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12474572 b7e13653115
          have b7e13655060 : y ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e13653154 x y
               grind)
            | exact superpose b7e13653154 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e13653154 x y
               grind)
            | exact resolve b7e22 b7e13653154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13653154
          have b7e13655194 : False := by grind
          exact b7e13655194
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e78 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e177 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e78 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e178 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e177
               have r₂ := b8e24
               grind)
            | exact resolve b8e177 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177
          have b8e179 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e178
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e178
            | exact resolve b8e178 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e178
          have b8e180 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e179
               grind)
            | exact superpose b8e179 b8e20
            | exact resolve b8e20 b8e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179
          have b8e344 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e180
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e180
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e180 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180
          have b8e345 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e344
          have b8e347 : y = (M.op x y) := by
            first
            | (have r₁ := b8e345
               have r₂ := b8e21
               grind)
            | exact resolve b8e345 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e345
          have b8e349 : False := by grind
          exact b8e349

/-- `Equation3736`: `x ◇ y = (x ◇ z) ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_y_pxy_Equation3736 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = b :=
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
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
        have b1e27 : x = (k x y) := by grind
        clear b1e24
        have b1e45 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e47 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e45
        have b1e50 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e21
             grind)
          | exact resolve b1e47 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e52 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e50
          | exact resolve b1e50 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e53 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e52
          | exact resolve b1e52 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e52
        have b1e54 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e22
          | exact resolve b1e22 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e21
          | exact resolve b1e21 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e62 : False := by grind
        exact b1e62
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
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
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
        have b2e32 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 X0)) := by
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
        have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X0 X2) X3 (M.op X1 X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 (M.op X0 X0) X2
             have i₂ := b2e12 X0 X0 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 (M.op X0 X2) (M.op X1 X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op X0 X2) (M.op X1 X1)
             grind)
          | (have r₁ := b2e15 (M.op X0 X2) (M.op X0 X0)
             have r₂ := b2e12 X0 X0 X2
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 X0 X1 x
             have i₂ := b2e12 X1 X0 x
             grind)
          | exact superpose b2e12 b2e34
          | exact resolve b2e34 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e37 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b2e33 X0 x X2 X3
             have i₂ := b2e12 X0 X3 x
             grind)
          | exact superpose b2e12 b2e33
          | exact resolve b2e33 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e39 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op x X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X1 (M.op X0 X0)
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e12
          | exact resolve b2e12 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b2e39 x X1
             have i₂ := b2e12 x X1 x
             grind)
          | exact superpose b2e12 b2e39
          | exact resolve b2e39 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39
        have b2e43 : y ≠ y ∨ x = (M.op y x) ∨ x = (k y x) := by
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
        have b2e44 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (M.op (M.op X1 X1) (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 (M.op X1 X1) (M.op X0 X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e16
          | (have j0 := b2e16 (M.op X1 X1) (M.op X0 X2)
             grind)
          | (have r₁ := b2e16 (M.op X0 X0) (M.op X0 X2)
             have r₂ := b2e12 X0 X0 X2
             grind)
          | exact resolve b2e16 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46 : x = (k y x) ∨ x = (M.op y x) := by grind
        clear b2e43
        have b2e48 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e44 X0 X1 X2
             have i₂ := b2e37 X1 X1 (M.op X0 X2)
             grind)
          | exact superpose b2e37 b2e44
          | (have j0 := b2e44 X0 X1 X2
             grind)
          | (have r₁ := b2e44 (M.op X0 X2) X0 X2
             have r₂ := b2e37 X0 X2 X0
             grind)
          | (have r₁ := b2e44 X0 (M.op X0 X2) X2
             have r₂ := b2e37 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b2e44 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e51 : y = (M.op y y) := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e41 y
             grind)
          | exact superpose b2e41 b2e20
          | exact resolve b2e20 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ x = (M.op X0 x) ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b2e16 X0 x
             have i₂ := b2e41 X0
             grind)
          | exact superpose b2e41 b2e16
          | (have j0 := b2e16 X0 x
             grind)
          | exact resolve b2e16 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e41 X0
             grind)
          | exact superpose b2e41 b2e15
          | (have j0 := b2e15 y X0
             grind)
          | exact resolve b2e15 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : (M.op y x) = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b2e32 x
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e32
          | exact resolve b2e32 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e56 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 x X1
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e12
          | exact resolve b2e12 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b2e56 X0 x
             have i₂ := b2e37 X0 x (M.op y x)
             grind)
          | exact superpose b2e37 b2e56
          | exact resolve b2e56 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e65 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b2e15 y y
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e15
          | (have j0 := b2e15 y y
             grind)
          | (have r₁ := b2e15 y y
             have r₂ := b2e51
             grind)
          | exact resolve b2e15 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e68 : y = (k y y) := by grind
        clear b2e65
        have b2e76 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 (M.op X1 X1)
             have i₂ := b2e36 X1 X0
             grind)
          | exact superpose b2e36 b2e15
          | (have j0 := b2e15 X0 (M.op X1 X1)
             grind)
          | (have r₁ := b2e15 X1 (M.op X1 X1)
             have r₂ := b2e36 X1 X1
             grind)
          | exact resolve b2e15 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e100 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X2) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 (M.op X0 X2) X1
             have i₂ := b2e37 X0 X2 X1
             grind)
          | exact superpose b2e37 b2e15
          | (have j0 := b2e15 X0 X1
             grind)
          | exact resolve b2e15 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e101 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e36 (M.op X0 X1) X2
             have i₂ := b2e37 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b2e37 b2e36
          | exact resolve b2e36 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e122 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e27 X1 X0
             have i₂ := b2e17 X0 (τ X1)
             grind)
          | exact superpose b2e17 b2e27
          | (have j1 := b2e17 X0 (τ X1)
             grind)
          | exact resolve b2e27 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e127 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e160 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b2e35 y y x
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e35
          | exact resolve b2e35 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e167 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e35 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e168 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) y) := by
          intro X0
          first
          | (have j0 := b2e160 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e160
        have b2e226 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e61 y x
             grind)
          | exact superpose b2e61 b2e21
          | (have j1 := b2e61 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e61 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e61 x y
             grind)
          | exact resolve b2e21 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e228 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op (σ X1) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e37 (σ X1) (σ X0) X2
             have i₂ := b2e61 X0 X1
             grind)
          | exact superpose b2e61 b2e37
          | (have j1 := b2e61 X0 X1
             grind)
          | exact resolve b2e37 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e232 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e61 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e234 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e232 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e232
        have b2e238 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e226
        have b2e248 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e238
             have r₂ := b2e22
             grind)
          | exact resolve b2e238 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238
        have b2e256 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
        have b2e281 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e48 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e327 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e248
             grind)
          | exact superpose b2e248 b2e22
          | exact resolve b2e22 b2e248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e328 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k y x)) X0) := by
          intro X0
          first
          | (have i₁ := b2e37 (σ y) (σ x) X0
             have i₂ := b2e248
             grind)
          | exact superpose b2e248 b2e37
          | exact resolve b2e37 b2e248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e335 : (σ x) ≠ (σ x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e327
             have i₂ := b2e46
             grind)
          | exact superpose b2e46 b2e327
          | exact resolve b2e327 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e337 : x = (M.op y x) := by grind
        clear b2e335
        have b2e342 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e167 (σ X1) (σ X0)
             have i₂ := b2e61 X0 X1
             grind)
          | exact superpose b2e61 b2e167
          | (have j1 := b2e61 X0 X1
             grind)
          | exact resolve b2e167 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e353 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e167 (M.op X0 X1) X2
             have i₂ := b2e37 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b2e37 b2e167
          | exact resolve b2e167 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e355 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b2e167 x X0
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e167
          | exact resolve b2e167 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e360 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) x) := by
          intro X0
          first
          | (have i₁ := b2e355 X0
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e355
          | exact resolve b2e355 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e355
        have b2e361 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e353 X0 X2 x
             have i₂ := b2e37 X0 X2 x
             grind)
          | exact superpose b2e37 b2e353
          | exact resolve b2e353 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e353
        have b2e370 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) x) := by
          intro X0
          first
          | (have i₁ := b2e360 x
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e360
          | exact resolve b2e360 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e360
        have b2e380 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e337
             grind)
          | exact resolve b2e15 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e385 : y = (k y x) := by grind
        clear b2e380
        have b2e409 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 (M.op X1 X2)) ∨ (k X0 (M.op X1 (M.op X1 X2))) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X1 (M.op X1 X2))
             have i₂ := b2e101 X1 X2 X0
             grind)
          | exact superpose b2e101 b2e15
          | (have j0 := b2e15 X0 (M.op X1 (M.op X1 X2))
             grind)
          | (have r₁ := b2e15 X2 (M.op X2 (M.op X2 X1))
             have r₂ := b2e101 X2 X1 X2
             grind)
          | exact resolve b2e15 b2e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e101
        have b2e460 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e327
             have i₂ := b2e385
             grind)
          | exact superpose b2e385 b2e327
          | exact resolve b2e327 b2e385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e327
        have b2e512 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e76 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e548 : x = (k x (M.op y x)) := by
          first
          | (have i₁ := b2e512 x
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e512
          | exact resolve b2e512 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e512
        have b2e557 : x = (k x x) := by
          first
          | (have i₁ := b2e548
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e548
          | exact resolve b2e548 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e548
        have b2e770 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e234 (M.op X0 X0)
             have i₂ := b2e167 X0 X0
             grind)
          | exact superpose b2e167 b2e234
          | (have j0 := b2e234 (M.op X0 X0)
             grind)
          | exact resolve b2e234 b2e167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e773 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e234 x
             have i₂ := b2e557
             grind)
          | exact superpose b2e557 b2e234
          | (have j0 := b2e234 x
             grind)
          | exact resolve b2e234 b2e557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e774 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e234 y
             have i₂ := b2e68
             grind)
          | exact superpose b2e68 b2e234
          | (have j0 := b2e234 y
             grind)
          | exact resolve b2e234 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e776 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e234 (τ X0)
             have i₂ := b2e27 X0 (τ X0)
             grind)
          | exact superpose b2e27 b2e234
          | (have j0 := b2e234 (τ X0)
             grind)
          | exact resolve b2e234 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234
        have b2e777 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e774
        have b2e778 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e773
        have b2e779 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have j0 := b2e770 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e770
        have b2e781 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e776 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e776
          | (have j0 := b2e776 X0
             grind)
          | exact resolve b2e776 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e776
        have b2e784 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e781 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e781
          | (have j0 := b2e781 X0
             grind)
          | exact resolve b2e781 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e781
        have b2e857 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e167 (σ x) X0
             have i₂ := b2e778
             grind)
          | exact superpose b2e778 b2e167
          | exact resolve b2e167 b2e778
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e167
        have b2e933 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e784 (τ X0)
             have i₂ := b2e256 X0 X0
             grind)
          | exact superpose b2e256 b2e784
          | (have j0 := b2e784 (τ X0)
             grind)
          | exact resolve b2e784 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e784
        have b2e1363 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op y (τ X0))) ∨ x = (M.op (τ X0) x) ∨ (τ X0) = (M.op y (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e122 x x
             have i₂ := b2e41 (τ x)
             grind)
          | exact superpose b2e41 b2e122
          | (have j0 := b2e122 x X0
             grind)
          | exact resolve b2e122 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122
        have b2e1402 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e857 (σ X0)
             have i₂ := b2e61 X0 x
             grind)
          | exact superpose b2e61 b2e857
          | (have j1 := b2e61 X0 x
             grind)
          | exact resolve b2e857 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e1413 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k (τ (M.op (σ x) X0)) x) := by
          intro X0
          first
          | (have i₁ := b2e31 (M.op (σ x) X0) x
             have i₂ := b2e857 X0
             grind)
          | exact superpose b2e857 b2e31
          | exact resolve b2e31 b2e857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e857
        have b2e1422 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b2e1402 X0
             have j1 := b2e15 (σ X0) (σ x)
             grind)
          | (have r₁ := b2e1402 X0
             have r₂ := b2e15 (σ X0) (σ x)
             grind)
          | exact resolve b2e1402 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1402
        have b2e1426 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e1422 X0
             have i₂ := b2e18 X0 x
             grind)
          | exact superpose b2e18 b2e1422
          | (have j0 := b2e1422 X0
             grind)
          | exact resolve b2e1422 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1422
        have b2e1493 : ∀ X0 : G, x = (k x (M.op y (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b2e361 y x x
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e361
          | exact resolve b2e361 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e361
        have b2e2062 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (σ X2) X1) ∨ (M.op X0 (σ X2)) = (σ (k (τ X0) X2)) ∨ (σ X2) = (M.op X0 (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e228 (τ X0) X1 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e228
          | exact resolve b2e228 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2083 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (σ X1) X2) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e228 X0 (τ X0) X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e228
          | exact resolve b2e228 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2116 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (M.op (σ X0) X3) = (M.op (σ X1) X3) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e37 (σ X0) (σ X1) X2
             have i₂ := b2e228 X0 X1 X3
             grind)
          | exact superpose b2e228 b2e37
          | (have j1 := b2e228 X0 X1 X3
             grind)
          | exact resolve b2e37 b2e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2138 : ∀ X0 : G, (σ y) ≠ (M.op (σ X0) (σ y)) ∨ (M.op (σ x) (σ X0)) = (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e228 x X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e228 X0 x (σ y)
             grind)
          | exact superpose b2e228 b2e21
          | (have j1 := b2e228 x X0 x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e228 x y x
             grind)
          | exact resolve b2e21 b2e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2234 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e228 X0 X1 (σ X1)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e228
        have b2e2270 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X2) = (M.op (σ X1) X2) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e2083 X0 X1 X2
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e2083
          | (have j0 := b2e2083 X0 X1 X2
             grind)
          | exact resolve b2e2083 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2083
        have b2e2276 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (M.op X0 X1) = (M.op (σ X2) X1) ∨ (σ X2) = (M.op X0 (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e2062 X0 X1 X2
             have i₂ := b2e26 X0 X2
             grind)
          | exact superpose b2e26 b2e2062
          | (have j0 := b2e2062 X0 X1 X2
             grind)
          | exact resolve b2e2062 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2062
        have b2e4431 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
          first
          | (have i₁ := b2e933 x
             have i₂ := b2e557
             grind)
          | exact superpose b2e557 b2e933
          | (have j0 := b2e933 x
             grind)
          | exact resolve b2e933 b2e557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4432 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
          first
          | (have i₁ := b2e933 y
             have i₂ := b2e68
             grind)
          | exact superpose b2e68 b2e933
          | (have j0 := b2e933 y
             grind)
          | exact resolve b2e933 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68 b2e933
        have b2e4439 : (τ y) = (M.op (τ y) (τ y)) := by grind
        clear b2e4432
        have b2e4440 : (τ x) = (M.op (τ x) (τ x)) := by grind
        clear b2e4431
        have b2e5019 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e409 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e409
        have b2e5117 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (M.op (τ X0) X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e26 X0 (M.op (τ X0) (M.op (τ X0) X1))
             have i₂ := b2e5019 (τ X0) X1
             grind)
          | exact superpose b2e5019 b2e26
          | exact resolve b2e26 b2e5019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5019
        have b2e5126 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) X1)))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e5117 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e5117
          | exact resolve b2e5117 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5117
        have b2e5416 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1))))) := by
          intro X0 X1
          first
          | (have i₁ := b2e26 X0 (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)))
             have i₂ := b2e5126 (τ X0) X1
             grind)
          | exact superpose b2e5126 b2e26
          | exact resolve b2e26 b2e5126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5126
        have b2e5429 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1))))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e5416 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e5416
          | exact resolve b2e5416 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5416
        have b2e11617 : ∀ X0 : G, (σ (M.op y X0)) = (k (σ x) (σ X0)) ∨ x = (M.op X0 x) ∨ (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1363 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1363
          | exact resolve b2e1363 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1363
        have b2e11685 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op y X0)) ∨ x = (M.op X0 x) ∨ (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e11617 X0
             have i₂ := b2e18 x X0
             grind)
          | exact superpose b2e18 b2e11617
          | (have j0 := b2e11617 X0
             grind)
          | exact resolve b2e11617 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11617
        have b2e12686 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e2270 X0 (τ X0) X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e2270
          | exact resolve b2e2270 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2270
        have b2e15956 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e778
             have i₂ := b2e2276 X0 (σ x) x
             grind)
          | (have i₁ := b2e778
             have i₂ := b2e2276 (σ x) (σ x) x
             grind)
          | exact superpose b2e2276 b2e778
          | (have j1 := b2e2276 X0 x x
             grind)
          | exact resolve b2e778 b2e2276
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e15960 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e777
             have i₂ := b2e2276 X0 (σ y) y
             grind)
          | (have i₁ := b2e777
             have i₂ := b2e2276 (σ y) (σ y) x
             grind)
          | exact superpose b2e2276 b2e777
          | (have j1 := b2e2276 X0 x y
             grind)
          | exact resolve b2e777 b2e2276
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2276
        have b2e16030 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e15960 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15960
        have b2e16031 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b2e15956 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15956
        have b2e18260 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ (k y x))) = (σ (k x (k y x))) ∨ (σ (k y x)) = (M.op (σ x) (σ (k y x))) := by
          first
          | (have i₁ := b2e2138 (k y x)
             have i₂ := b2e328 (σ y)
             grind)
          | exact superpose b2e328 b2e2138
          | (have j0 := b2e2138 (k y x)
             grind)
          | exact resolve b2e2138 b2e328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e328 b2e2138
        have b2e18270 : (M.op (σ x) (σ (k y x))) = (σ (k x (k y x))) ∨ (σ (k y x)) = (M.op (σ x) (σ (k y x))) := by
          first
          | (have r₁ := b2e18260
             have r₂ := b2e777
             grind)
          | exact resolve b2e18260 b2e777
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18260
        have b2e18276 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k y x)) = (M.op (σ x) (σ (k y x))) := by
          first
          | (have i₁ := b2e18270
             have i₂ := b2e385
             grind)
          | exact superpose b2e385 b2e18270
          | exact resolve b2e18270 b2e385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18270
        have b2e18277 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ x) (σ (k y x))) := by
          first
          | (have i₁ := b2e18276
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e18276
          | exact resolve b2e18276 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18276
        have b2e18278 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e18277
             have i₂ := b2e385
             grind)
          | exact superpose b2e385 b2e18277
          | exact resolve b2e18277 b2e385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18277
        have b2e18279 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e18278
             have r₂ := b2e21
             grind)
          | exact resolve b2e18278 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18278
        have b2e19128 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 (σ y))) ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e31 X0 y
             have i₂ := b2e16030 X0
             grind)
          | exact superpose b2e16030 b2e31
          | (have j1 := b2e16030 X0
             grind)
          | exact resolve b2e31 b2e16030
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e19307 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e31 X0 x
             have i₂ := b2e16031 X0
             grind)
          | exact superpose b2e16031 b2e31
          | (have j1 := b2e16031 X0
             grind)
          | exact resolve b2e31 b2e16031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e25327 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (M.op (σ (τ X0)) X3) = (M.op (σ (τ X1)) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e2116 (τ X0) (τ X1) X2 X3
             have i₂ := b2e256 X1 X0
             grind)
          | exact superpose b2e256 b2e2116
          | (have j0 := b2e2116 (τ X0) (τ X1) X2 X3
             grind)
          | exact resolve b2e2116 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e25797 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ (M.op X1 X1))) ∨ (M.op (σ X0) X2) = (M.op (σ (k X0 (M.op X1 X1))) X2) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ (M.op X1 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e779 X1
             have i₂ := b2e2116 X0 (M.op X1 X1) X2 (σ (M.op X1 X1))
             grind)
          | (have i₁ := b2e779 X0
             have i₂ := b2e2116 (M.op X0 X0) X1 X2 (σ (M.op X0 X0))
             grind)
          | exact superpose b2e2116 b2e779
          | (have j1 := b2e2116 X0 (M.op X1 X1) X2 x
             grind)
          | exact resolve b2e779 b2e2116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e779 b2e2116
        have b2e25894 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 (M.op X1 X1))) X2) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ (M.op X1 X1))) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e25797 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25797
        have b2e26005 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X2) = (M.op (k X0 X1) X2) ∨ (M.op (σ (τ X0)) X3) = (M.op (σ (τ X1)) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e25327 X0 X1 X2 X3
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e25327
          | (have j0 := b2e25327 X0 X1 X2 X3
             grind)
          | exact resolve b2e25327 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25327
        have b2e26043 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (M.op (σ (τ X0)) X3) = (M.op (σ (τ X1)) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26005 X0 X1 X2 X3
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e26005
          | (have j0 := b2e26005 X0 X1 X2 X3
             grind)
          | exact resolve b2e26005 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26005
        have b2e26067 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X3) = (M.op X1 X3) ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26043 X0 X1 X2 X3
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e26043
          | (have j0 := b2e26043 X0 X1 X2 X3
             grind)
          | exact resolve b2e26043 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26043
        have b2e26084 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op X1 X3) ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26067 X0 X1 X2 X3
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e26067
          | (have j0 := b2e26067 X0 X1 X2 X3
             grind)
          | exact resolve b2e26067 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26067
        have b2e26097 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X3) = (M.op X1 X3) ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26084 X0 X0 X2 X3
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e26084
          | (have j0 := b2e26084 X0 X1 X2 X3
             grind)
          | exact resolve b2e26084 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26084
        have b2e26106 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (M.op X0 X3) = (M.op X1 X3) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26097 X0 X1 X2 X3
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e26097
          | (have j0 := b2e26097 X0 X1 X2 X3
             grind)
          | exact resolve b2e26097 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26097
        have b2e26596 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (M.op X0 X0)) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e342 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e342
          | exact resolve b2e342 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e342
        have b2e26726 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (M.op X0 X0)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e26596 X0 X1
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e26596
          | (have j0 := b2e26596 X0 X1
             grind)
          | exact resolve b2e26596 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26596
        have b2e26755 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (k (τ X0) x)) ∨ (σ (k (τ X0) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1426 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1426
          | exact resolve b2e1426 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26871 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (k (σ X0) (σ x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e15 (σ X0) (σ x)
             have i₂ := b2e1426 X0
             grind)
          | exact superpose b2e1426 b2e15
          | (have j0 := b2e15 (σ X0) (σ x)
             have j1 := b2e1426 X0
             grind)
          | exact resolve b2e15 b2e1426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26874 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 x)) X1) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e37 (σ X0) (σ x) X1
             have i₂ := b2e1426 X0
             grind)
          | exact superpose b2e1426 b2e37
          | (have j1 := b2e1426 X0
             grind)
          | exact resolve b2e37 b2e1426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1426
        have b2e26908 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) ∨ (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e26871 X0
             have i₂ := b2e18 X0 x
             grind)
          | exact superpose b2e18 b2e26871
          | (have j0 := b2e26871 X0
             grind)
          | exact resolve b2e26871 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26871
        have b2e26909 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have j0 := b2e26908 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26908
        have b2e26957 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ (k (τ X0) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e26755 X0
             have i₂ := b2e26 X0 x
             grind)
          | exact superpose b2e26 b2e26755
          | (have j0 := b2e26755 X0
             grind)
          | exact resolve b2e26755 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26755
        have b2e26997 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e26957 X0
             have i₂ := b2e26 X0 x
             grind)
          | exact superpose b2e26 b2e26957
          | (have j0 := b2e26957 X0
             grind)
          | exact resolve b2e26957 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26957
        have b2e27318 : ∀ X0 : G, (σ x) ≠ (k X0 (σ x)) ∨ (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e26909 (τ X0)
             have i₂ := b2e26 X0 x
             grind)
          | exact superpose b2e26 b2e26909
          | exact resolve b2e26909 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27345 : ∀ X0 : G, (σ x) ≠ (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27318 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e27318
          | (have j0 := b2e27318 X0
             grind)
          | exact resolve b2e27318 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27318
        have b2e28063 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e2234 (τ X0) (τ X1)
             have i₂ := b2e256 X1 X0
             grind)
          | exact superpose b2e256 b2e2234
          | (have j0 := b2e2234 (τ X0) (τ X1)
             grind)
          | exact resolve b2e2234 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28146 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e2234 X0 x
             have i₂ := b2e778
             grind)
          | exact superpose b2e778 b2e2234
          | (have j0 := b2e2234 X0 x
             grind)
          | exact resolve b2e2234 b2e778
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2234
        have b2e28165 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b2e28146 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28146
        have b2e28212 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e28063 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e28063
          | (have j0 := b2e28063 X0 X1
             grind)
          | exact resolve b2e28063 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28063
        have b2e28267 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e28212 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e28212
          | (have j0 := b2e28212 X0 X1
             grind)
          | exact resolve b2e28212 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28212
        have b2e28298 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e28267 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e28267
          | (have j0 := b2e28267 X0 X1
             grind)
          | exact resolve b2e28267 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28267
        have b2e28324 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e28298 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e28298
          | (have j0 := b2e28298 X0 X1
             grind)
          | exact resolve b2e28298 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28298
        have b2e28343 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e28324 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e28324
          | (have j0 := b2e28324 X0 X1
             grind)
          | exact resolve b2e28324 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28324
        have b2e28362 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e28343 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e28343
          | (have j0 := b2e28343 X0 X1
             grind)
          | exact resolve b2e28343 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28343
        have b2e29040 : ∀ X0 : G, (σ x) ≠ (k X0 (σ x)) ∨ (σ x) = (M.op (σ (τ X0)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e28165 (τ X0)
             have i₂ := b2e26 X0 x
             grind)
          | exact superpose b2e26 b2e28165
          | (have j0 := b2e28165 (τ X0)
             grind)
          | exact resolve b2e28165 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28165
        have b2e29068 : ∀ X0 : G, (σ x) ≠ (k X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e29040 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e29040
          | (have j0 := b2e29040 X0
             grind)
          | exact resolve b2e29040 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29040
        have b2e30007 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e31 X0 x
             have i₂ := b2e26997 X0
             grind)
          | exact superpose b2e26997 b2e31
          | (have j1 := b2e26997 X0
             grind)
          | exact resolve b2e31 b2e26997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30108 : ∀ X0 : G, (M.op X0 (σ x)) ≠ X0 ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have j0 := b2e26997 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31824 : (k (τ x) x) = (τ (M.op y (σ x))) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e30007 x
             have i₂ := b2e41 (σ x)
             grind)
          | exact superpose b2e41 b2e30007
          | (have j0 := b2e30007 x
             grind)
          | exact resolve b2e30007 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30007
        have b2e35163 : (k (τ x) y) = (τ (M.op y (σ y))) ∨ (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e19128 x
             have i₂ := b2e41 (σ y)
             grind)
          | exact superpose b2e41 b2e19128
          | (have j0 := b2e19128 y
             grind)
          | exact resolve b2e19128 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19128
        have b2e39759 : (k (τ x) x) = (τ (M.op y (σ x))) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e19307 x
             have i₂ := b2e41 (σ x)
             grind)
          | exact superpose b2e41 b2e19307
          | (have j0 := b2e19307 y
             grind)
          | exact resolve b2e19307 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39770 : (k (τ y) x) = (k (τ x) x) ∨ x = (k x (σ x)) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e31824
             have i₂ := b2e19307 y
             grind)
          | exact superpose b2e19307 b2e31824
          | (have j1 := b2e19307 y
             grind)
          | exact resolve b2e31824 b2e19307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31824
        have b2e39842 : (k (τ y) x) = (k (τ x) x) ∨ x = (k x (σ x)) := by
          first
          | (have j1 := b2e54 (σ x)
             grind)
          | (have r₁ := b2e39770
             have r₂ := b2e54 (σ x)
             grind)
          | exact resolve b2e39770 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39770
        have b2e40249 : (k x (σ x)) = (σ (k (τ y) x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e26 x x
             have i₂ := b2e39842
             grind)
          | exact superpose b2e39842 b2e26
          | exact resolve b2e26 b2e39842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40332 : (k y (σ x)) = (k x (σ x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e40249
             have i₂ := b2e26 y x
             grind)
          | exact superpose b2e26 b2e40249
          | exact resolve b2e40249 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40249
        have b2e41357 : x ≠ (k y (σ x)) ∨ x = (k x (σ x)) := by grind
        clear b2e40332
        have b2e223527 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op (k X0 (σ x)) X1) ∨ (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e26874 (τ X0) X1
             have i₂ := b2e26 X0 x
             grind)
          | exact superpose b2e26 b2e26874
          | exact resolve b2e26874 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26874
        have b2e223650 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 (σ x)) X1) ∨ (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e223527 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e223527
          | (have j0 := b2e223527 X0 X1
             grind)
          | exact resolve b2e223527 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e223527
        have b2e223669 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 (σ x)) X1) ∨ (k X0 (σ x)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e223650 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e223650
          | (have j0 := b2e223650 X0 X1
             grind)
          | exact resolve b2e223650 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e223650
        have b2e224473 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (k X0 (σ x)) ∨ (k X0 (σ x)) = (k (k X0 (σ x)) (σ x)) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e30108 (k X0 (σ x))
             have i₂ := b2e223669 X0 (σ x)
             grind)
          | exact superpose b2e223669 b2e30108
          | (have j0 := b2e30108 (k X0 (σ x))
             have j1 := b2e223669 (k X0 (σ x)) x
             grind)
          | exact resolve b2e30108 b2e223669
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30108 b2e223669
        have b2e224489 : ∀ X0 : G, (k X0 (σ x)) = (k (k X0 (σ x)) (σ x)) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have j0 := b2e224473 X0
             have j1 := b2e26997 (k X0 (σ x))
             grind)
          | (have r₁ := b2e224473 X0
             have r₂ := b2e26997 X0
             grind)
          | exact resolve b2e224473 b2e26997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26997 b2e224473
        have b2e224512 : ∀ X0 : G, (k X0 (σ x)) = (σ (k (k (τ X0) x) x)) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e224489 X0
             have i₂ := b2e30 X0 x x
             grind)
          | exact superpose b2e30 b2e224489
          | (have j0 := b2e224489 X0
             grind)
          | exact resolve b2e224489 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e224489
        have b2e338805 : (k x (σ x)) = (σ (k (k (τ y) x) x)) ∨ x = (k x (σ x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e224512 x
             have i₂ := b2e39842
             grind)
          | exact superpose b2e39842 b2e224512
          | (have j0 := b2e224512 x
             grind)
          | exact resolve b2e224512 b2e39842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39842 b2e224512
        have b2e338856 : (k x (σ x)) = (σ (k (k (τ y) x) x)) ∨ x = (k x (σ x)) := by grind
        clear b2e338805
        have b2e412504 : ∀ X0 : G, (τ x) = (M.op X0 (τ x)) ∨ (M.op X0 (τ x)) = (k X0 (τ x)) ∨ (τ x) = (M.op X0 (τ x)) := by
          intro X0
          first
          | (have i₁ := b2e4440
             have i₂ := b2e12686 X0 (τ x) (τ x)
             grind)
          | (have i₁ := b2e4440
             have i₂ := b2e12686 (τ x) x (τ x)
             grind)
          | exact superpose b2e12686 b2e4440
          | (have j1 := b2e12686 X0 (τ x) x
             grind)
          | exact resolve b2e4440 b2e12686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e412510 : ∀ X0 : G, (τ y) = (M.op X0 (τ y)) ∨ (M.op X0 (τ y)) = (k X0 (τ y)) ∨ (τ y) = (M.op X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b2e4439
             have i₂ := b2e12686 X0 (τ y) (τ y)
             grind)
          | (have i₁ := b2e4439
             have i₂ := b2e12686 (τ y) x (τ y)
             grind)
          | exact superpose b2e12686 b2e4439
          | (have j1 := b2e12686 X0 (τ y) x
             grind)
          | exact resolve b2e4439 b2e12686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e412523 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) y) ∨ (M.op X0 y) = (k X0 y) ∨ y = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e168 x
             have i₂ := b2e12686 y X1 x
             grind)
          | (have i₁ := b2e168 x
             have i₂ := b2e12686 X0 y x
             grind)
          | exact superpose b2e12686 b2e168
          | (have j1 := b2e12686 X0 y x
             grind)
          | exact resolve b2e168 b2e12686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e412661 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e12686 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12686
        have b2e412676 : ∀ X0 : G, (M.op X0 (τ y)) = (k X0 (τ y)) ∨ (τ y) = (M.op X0 (τ y)) := by
          intro X0
          first
          | (have j0 := b2e412510 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412510
        have b2e412677 : ∀ X0 : G, (M.op X0 (τ x)) = (k X0 (τ x)) ∨ (τ x) = (M.op X0 (τ x)) := by
          intro X0
          first
          | (have j0 := b2e412504 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412504
        have b2e412772 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) y) ∨ (M.op X0 y) = (k X0 y) := by
          intro X0 X1
          first
          | (have j0 := b2e412523 X0 X1
             have j1 := b2e100 X0 y X1
             grind)
          | (have r₁ := b2e412523 X0 X1
             have r₂ := b2e100 X0 y x
             grind)
          | exact resolve b2e412523 b2e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412523
        have b2e413350 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) y) ∨ (M.op (M.op X0 X2) y) = (k (M.op X0 X2) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e412772 (M.op X0 X2) x
             have i₂ := b2e37 X0 X2 x
             grind)
          | exact superpose b2e37 b2e412772
          | (have j0 := b2e412772 X0 X1
             grind)
          | exact resolve b2e412772 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412772
        have b2e413457 : ∀ X0 X1 X2 : G, (M.op X0 y) = (k (M.op X0 X2) y) ∨ (M.op X0 X1) = (k (M.op X0 X1) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e413350 X0 X1 X2
             have i₂ := b2e37 X0 X2 y
             grind)
          | exact superpose b2e37 b2e413350
          | (have j0 := b2e413350 X0 X1 X2
             grind)
          | exact resolve b2e413350 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e413350
        have b2e413680 : ∀ X0 : G, (k (σ X0) y) = (σ (M.op X0 (τ y))) ∨ (τ y) = (M.op X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b2e27 y X0
             have i₂ := b2e412676 X0
             grind)
          | exact superpose b2e412676 b2e27
          | (have j1 := b2e412676 X0
             grind)
          | exact resolve b2e27 b2e412676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412676
        have b2e414054 : ∀ X0 : G, (k (σ X0) x) = (σ (M.op X0 (τ x))) ∨ (τ x) = (M.op X0 (τ x)) := by
          intro X0
          first
          | (have i₁ := b2e27 x X0
             have i₂ := b2e412677 X0
             grind)
          | exact superpose b2e412677 b2e27
          | (have j1 := b2e412677 X0
             grind)
          | exact resolve b2e27 b2e412677
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e414113 : ∀ X0 : G, (τ (k X0 x)) = (M.op (τ X0) (τ x)) ∨ (τ x) = (M.op (τ X0) (τ x)) := by
          intro X0
          first
          | (have i₁ := b2e256 x X0
             have i₂ := b2e412677 (τ X0)
             grind)
          | exact superpose b2e412677 b2e256
          | (have j1 := b2e412677 (τ X0)
             grind)
          | exact resolve b2e256 b2e412677
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412677
        have b2e417951 : ∀ X0 : G, x ≠ (M.op y x) ∨ (M.op X0 x) = (k X0 x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e412661 X0 x
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e412661
          | (have j0 := b2e412661 X0 x
             grind)
          | exact resolve b2e412661 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412661
        have b2e417965 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b2e417951 X0
             grind)
          | (have r₁ := b2e417951 X0
             have r₂ := b2e337
             grind)
          | exact resolve b2e417951 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e417951
        have b2e420361 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) x)) ∨ x = (M.op (σ X0) x) := by
          intro X0
          first
          | (have i₁ := b2e127 X0 x
             have i₂ := b2e417965 (σ X0)
             grind)
          | exact superpose b2e417965 b2e127
          | (have j1 := b2e417965 (σ X0)
             grind)
          | exact resolve b2e127 b2e417965
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e426369 : ∀ X0 : G, (k (τ X0) (τ x)) = (τ (M.op X0 x)) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e420361 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e420361
          | exact resolve b2e420361 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e420361
        have b2e426435 : ∀ X0 : G, (τ (k X0 x)) = (τ (M.op X0 x)) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e426369 X0
             have i₂ := b2e256 x X0
             grind)
          | exact superpose b2e256 b2e426369
          | (have j0 := b2e426369 X0
             grind)
          | exact resolve b2e426369 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e426369
        have b2e427312 : ∀ X0 X1 : G, (τ (k (k X0 x) X1)) = (k (τ (M.op X0 x)) (τ X1)) ∨ x = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e256 X1 (k X0 x)
             have i₂ := b2e426435 X0
             grind)
          | exact superpose b2e426435 b2e256
          | (have j1 := b2e426435 X0
             grind)
          | exact resolve b2e256 b2e426435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e426435
        have b2e427395 : ∀ X0 X1 : G, (τ (k (k X0 x) X1)) = (τ (k (M.op X0 x) X1)) ∨ x = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e427312 X0 X1
             have i₂ := b2e256 X1 (M.op X0 x)
             grind)
          | exact superpose b2e256 b2e427312
          | (have j0 := b2e427312 X0 X1
             grind)
          | exact resolve b2e427312 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e256 b2e427312
        have b2e430422 : (k (σ x) y) = (σ (M.op y (τ y))) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e413680 x
             have i₂ := b2e41 (τ y)
             grind)
          | exact superpose b2e41 b2e413680
          | (have j0 := b2e413680 y
             grind)
          | exact resolve b2e413680 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e430719 : (k (σ x) x) = (σ (M.op y (τ x))) ∨ (τ x) = (M.op y (τ x)) := by
          first
          | (have i₁ := b2e414054 x
             have i₂ := b2e41 (τ x)
             grind)
          | exact superpose b2e41 b2e414054
          | (have j0 := b2e414054 y
             grind)
          | exact resolve b2e414054 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e414054
        have b2e437678 : (k (σ y) y) = (k (σ x) y) ∨ (τ y) = (M.op y (τ y)) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e413680 y
             have i₂ := b2e430422
             grind)
          | exact superpose b2e430422 b2e413680
          | (have j0 := b2e413680 y
             grind)
          | exact resolve b2e413680 b2e430422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e430422
        have b2e437715 : (k (σ y) y) = (k (σ x) y) ∨ (τ y) = (M.op y (τ y)) := by grind
        clear b2e437678
        have b2e446380 : ∀ X0 : G, (M.op (τ x) y) = (k (M.op (τ x) X0) y) ∨ (τ x) = (k (τ x) y) := by
          intro X0
          first
          | (have i₁ := b2e413457 (τ x) (τ x) x
             have i₂ := b2e4440
             grind)
          | exact superpose b2e4440 b2e413457
          | (have j0 := b2e413457 (τ x) x X0
             grind)
          | exact resolve b2e413457 b2e4440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e413457
        have b2e446498 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e28362 X0 (M.op X1 X1)
             have i₂ := b2e12 X1 X1 X1
             grind)
          | exact superpose b2e12 b2e28362
          | (have j0 := b2e28362 X1 (M.op X0 X0)
             grind)
          | exact resolve b2e28362 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28362
        have b2e446562 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e446498 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e446498
        have b2e446581 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 (M.op X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e446562 X0 X1
             have i₂ := b2e36 X0 X1
             grind)
          | exact superpose b2e36 b2e446562
          | (have j0 := b2e446562 X0 X1
             grind)
          | exact resolve b2e446562 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e446562
        have b2e448752 : ∀ X0 : G, (M.op y x) ≠ (k X0 (M.op y x)) ∨ (M.op y x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e446581 x x
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e446581
          | exact resolve b2e446581 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e448753 : ∀ X0 : G, y ≠ (k X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e446581 y x
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e446581
          | exact resolve b2e446581 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e446581
        have b2e448787 : ∀ X0 : G, x ≠ (k X0 x) ∨ (M.op y x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e448752 X0
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e448752
          | (have j0 := b2e448752 X0
             grind)
          | exact resolve b2e448752 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e448752
        have b2e448793 : ∀ X0 : G, x ≠ (k X0 x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e448787 X0
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e448787
          | (have j0 := b2e448787 X0
             grind)
          | exact resolve b2e448787 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e448787
        have b2e449604 : ∀ X0 : G, x ≠ (τ (M.op (σ x) X0)) ∨ x = (M.op (τ (M.op (σ x) X0)) x) := by
          intro X0
          first
          | (have i₁ := b2e448793 (τ (M.op (σ x) X0))
             have i₂ := b2e1413 X0
             grind)
          | exact superpose b2e1413 b2e448793
          | (have j0 := b2e448793 (τ (M.op (σ x) X0))
             grind)
          | exact resolve b2e448793 b2e1413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1413
        have b2e451338 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) y) ∨ (M.op X0 X2) = (M.op (k X0 y) X2) ∨ y = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e168 x
             have i₂ := b2e26106 y X1 X2 x
             grind)
          | (have i₁ := b2e168 x
             have i₂ := b2e26106 X0 y X2 x
             grind)
          | exact superpose b2e26106 b2e168
          | (have j1 := b2e26106 X0 y X2 x
             grind)
          | exact resolve b2e168 b2e26106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26106
        have b2e451354 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) y) ∨ (M.op X0 X2) = (M.op (k X0 y) X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e451338 X0 X1 X2
             have j1 := b2e100 X0 y X1
             grind)
          | (have r₁ := b2e451338 X0 X1 X2
             have r₂ := b2e100 X0 y X2
             grind)
          | exact resolve b2e451338 b2e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e451338
        have b2e452134 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (k (σ y) y) X0) ∨ (σ y) = (k (σ y) y) := by
          intro X0
          first
          | (have i₁ := b2e451354 (σ y) (σ y) x
             have i₂ := b2e777
             grind)
          | exact superpose b2e777 b2e451354
          | (have j0 := b2e451354 (σ y) x X0
             grind)
          | exact resolve b2e451354 b2e777
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e777 b2e451354
        have b2e452772 : (τ (M.op (σ y) (σ x))) = (k (τ (k (σ y) y)) x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e19307 (k (σ y) y)
             have i₂ := b2e452134 (σ x)
             grind)
          | exact superpose b2e452134 b2e19307
          | (have j0 := b2e19307 (σ y)
             grind)
          | exact resolve b2e19307 b2e452134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19307 b2e452134
        have b2e452815 : (τ (M.op (σ y) (σ x))) = (k (τ (k (σ y) y)) x) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have r₁ := b2e452772
             have r₂ := b2e22
             grind)
          | exact resolve b2e452772 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e452772
        have b2e452829 : (τ (M.op (σ y) (σ x))) = (k (k y (τ y)) x) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e452815
             have i₂ := b2e127 y y
             grind)
          | exact superpose b2e127 b2e452815
          | exact resolve b2e452815 b2e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e452815
        have b2e452830 : (τ (σ (k y x))) = (k (k y (τ y)) x) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e452829
             have i₂ := b2e248
             grind)
          | exact superpose b2e248 b2e452829
          | exact resolve b2e452829 b2e248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e452829
        have b2e452831 : (k y x) = (k (k y (τ y)) x) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e452830
             have i₂ := b2e13 (k y x)
             grind)
          | exact superpose b2e13 b2e452830
          | exact resolve b2e452830 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e452830
        have b2e452832 : y = (k (k y (τ y)) x) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e452831
             have i₂ := b2e385
             grind)
          | exact superpose b2e385 b2e452831
          | exact resolve b2e452831 b2e385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e452831
        have b2e458599 : ∀ X0 X1 : G, (k (k X0 x) X1) = (σ (τ (k (M.op X0 x) X1))) ∨ x = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e14 (k (k X0 x) X1)
             have i₂ := b2e427395 X0 X1
             grind)
          | exact superpose b2e427395 b2e14
          | (have j1 := b2e427395 X0 X1
             grind)
          | exact resolve b2e14 b2e427395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e427395
        have b2e458626 : ∀ X0 X1 : G, (k (k X0 x) X1) = (k (M.op X0 x) X1) ∨ x = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e458599 X0 X1
             have i₂ := b2e14 (k (M.op X0 x) X1)
             grind)
          | exact superpose b2e14 b2e458599
          | (have j0 := b2e458599 X0 X1
             grind)
          | exact resolve b2e458599 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e458599
        have b2e460631 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e26726 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e26726
          | exact resolve b2e26726 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26726
        have b2e467751 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 (τ x))) X1) ∨ (σ (τ x)) = (M.op (σ X0) (σ (τ x))) := by
          intro X0 X1
          first
          | (have i₁ := b2e25894 X0 (τ x) x
             have i₂ := b2e4440
             grind)
          | exact superpose b2e4440 b2e25894
          | exact resolve b2e25894 b2e4440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4440 b2e25894
        have b2e467774 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (k (σ X0) x) X1) ∨ (σ (τ x)) = (M.op (σ X0) (σ (τ x))) := by
          intro X0 X1
          first
          | (have i₁ := b2e467751 X0 X1
             have i₂ := b2e27 x X0
             grind)
          | exact superpose b2e27 b2e467751
          | (have j0 := b2e467751 X0 X1
             grind)
          | exact resolve b2e467751 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e467751
        have b2e467783 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (k (σ X0) x) X1) ∨ x = (M.op (σ X0) x) := by
          intro X0 X1
          first
          | (have i₁ := b2e467774 X0 X1
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e467774
          | (have j0 := b2e467774 X0 X1
             grind)
          | exact resolve b2e467774 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e467774
        have b2e468370 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 x) X1) ∨ x = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e467783 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e467783
          | exact resolve b2e467783 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e467783
        have b2e478175 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e460631 X1 (M.op X0 X0)
             have i₂ := b2e12 X0 X0 X0
             grind)
          | exact superpose b2e12 b2e460631
          | (have j0 := b2e460631 X1 (M.op X0 X0)
             grind)
          | exact resolve b2e460631 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e460631
        have b2e478203 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e478175 X0 X1
             have j1 := b2e15 X1 (M.op X0 X0)
             grind)
          | (have r₁ := b2e478175 X0 X0
             have r₂ := b2e15 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e478175 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478175
        have b2e478206 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e478203 X0 X1
             have i₂ := b2e36 X0 X1
             grind)
          | exact superpose b2e36 b2e478203
          | (have j0 := b2e478203 X0 X1
             grind)
          | exact resolve b2e478203 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e478203
        have b2e478268 : ∀ X0 : G, (M.op X0 (τ y)) = (k X0 (τ y)) ∨ (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e478206 (τ y) x
             have i₂ := b2e4439
             grind)
          | exact superpose b2e4439 b2e478206
          | exact resolve b2e478206 b2e4439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4439
        have b2e478275 : ∀ X0 : G, (M.op X0 x) = (k X0 (M.op y x)) ∨ (k X0 (M.op y x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e478206 x x
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e478206
          | exact resolve b2e478206 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e478276 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e478206 y x
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e478206
          | exact resolve b2e478206 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e478302 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e478206 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478206
        have b2e478306 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ (k X0 (M.op y x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e478275 X0
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e478275
          | (have j0 := b2e478275 X0
             grind)
          | exact resolve b2e478275 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478275
        have b2e478314 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e478306 X0
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e478306
          | (have j0 := b2e478306 X0
             grind)
          | exact resolve b2e478306 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478306
        have b2e478973 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (k X0 (M.op (M.op y x) (M.op y x))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e478302 X0 (M.op y x)
             have i₂ := b2e57 X0
             grind)
          | exact superpose b2e57 b2e478302
          | (have j0 := b2e478302 X0 x
             grind)
          | exact resolve b2e478302 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e478302
        have b2e479161 : ∀ X0 : G, (k X0 (M.op y (M.op y x))) = X0 ∨ (M.op X0 x) ≠ X0 := by
          intro X0
          first
          | (have i₁ := b2e478973 X0
             have i₂ := b2e37 y x (M.op y x)
             grind)
          | exact superpose b2e37 b2e478973
          | (have j0 := b2e478973 X0
             grind)
          | (have r₁ := b2e478973 (M.op X0 x)
             have r₂ := b2e37 X0 x x
             grind)
          | exact resolve b2e478973 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478973
        have b2e479199 : ∀ X0 : G, (k X0 (M.op y x)) = X0 ∨ (M.op X0 x) ≠ X0 := by
          intro X0
          first
          | (have i₁ := b2e479161 X0
             have i₂ := b2e55
             grind)
          | exact superpose b2e55 b2e479161
          | (have j0 := b2e479161 X0
             grind)
          | exact resolve b2e479161 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e479161
        have b2e479214 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e479199 X0
             have i₂ := b2e337
             grind)
          | exact superpose b2e337 b2e479199
          | (have j0 := b2e479199 X0
             grind)
          | exact resolve b2e479199 b2e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e337 b2e479199
        have b2e479251 : ∀ X0 : G, (M.op X0 x) ≠ (k X0 x) ∨ (k X0 x) = (k (k X0 x) x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e479214 (k X0 x)
             have i₂ := b2e468370 X0 x
             grind)
          | exact superpose b2e468370 b2e479214
          | (have j0 := b2e479214 (k X0 x)
             have j1 := b2e468370 X0 x
             grind)
          | (have r₁ := b2e479214 x
             have r₂ := b2e468370 x x
             grind)
          | exact resolve b2e479214 b2e468370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e468370 b2e479214
        have b2e479265 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b2e479251 X0
             have j1 := b2e417965 X0
             grind)
          | (have r₁ := b2e479251 X0
             have r₂ := b2e417965 X0
             grind)
          | exact resolve b2e479251 b2e417965
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e479251
        have b2e480436 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e479265 X0
             have i₂ := b2e417965 X0
             grind)
          | exact superpose b2e417965 b2e479265
          | (have j0 := b2e479265 X0
             have j1 := b2e417965 X0
             grind)
          | exact resolve b2e479265 b2e417965
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e417965
        have b2e480659 : ∀ X0 : G, (k X0 x) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e458626 X0 x
             have i₂ := b2e479265 X0
             grind)
          | exact superpose b2e479265 b2e458626
          | (have j0 := b2e458626 X0 x
             have j1 := b2e479265 X0
             grind)
          | exact resolve b2e458626 b2e479265
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e458626 b2e479265
        have b2e480714 : ∀ X0 : G, (k X0 x) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b2e480659 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e480659
        have b2e480750 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b2e480436 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e480436
        have b2e480776 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) x) := by
          intro X0
          first
          | (have j0 := b2e480750 X0
             have j1 := b2e100 X0 x x
             grind)
          | (have r₁ := b2e480750 X0
             have r₂ := b2e100 X0 x x
             grind)
          | exact resolve b2e480750 b2e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100 b2e480750
        have b2e481156 : ∀ X0 X1 : G, (k (M.op X0 X1) x) = (k (M.op X0 x) x) ∨ x = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e480714 (M.op X0 x)
             have i₂ := b2e37 X0 x x
             grind)
          | exact superpose b2e37 b2e480714
          | (have j0 := b2e480714 X0
             grind)
          | exact resolve b2e480714 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e480714
        have b2e481420 : ∀ X0 X1 : G, (M.op X0 x) = (k (M.op X0 X1) x) ∨ x = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e481156 X0 X1
             have i₂ := b2e480776 X0
             grind)
          | exact superpose b2e480776 b2e481156
          | (have j0 := b2e481156 X0 X1
             grind)
          | exact resolve b2e481156 b2e480776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e480776 b2e481156
        have b2e482042 : ∀ X0 : G, (k (σ X0) y) = (σ (M.op X0 (τ y))) ∨ (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27 y X0
             have i₂ := b2e478268 X0
             grind)
          | exact superpose b2e478268 b2e27
          | (have j1 := b2e478268 X0
             grind)
          | exact resolve b2e27 b2e478268
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e482090 : y = (k (M.op y (τ y)) x) ∨ (σ y) = (k (σ y) y) ∨ y = (k y (τ y)) := by
          first
          | (have i₁ := b2e452832
             have i₂ := b2e478268 y
             grind)
          | exact superpose b2e478268 b2e452832
          | (have j1 := b2e478268 y
             grind)
          | exact resolve b2e452832 b2e478268
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e452832
        have b2e482092 : ∀ X0 : G, (M.op X0 (τ y)) ≠ X0 ∨ (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e478268 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478268
        have b2e482095 : y = (M.op y (τ y)) ∨ (σ y) = (k (σ y) y) ∨ y = (k y (τ y)) := by
          first
          | (have i₁ := b2e482090
             have i₂ := b2e370 (τ y)
             grind)
          | exact superpose b2e370 b2e482090
          | exact resolve b2e482090 b2e370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482090
        have b2e482107 : (σ y) = (k (σ y) y) ∨ y = (k y (τ y)) := by
          first
          | (have j1 := b2e482092 y
             grind)
          | (have r₁ := b2e482095
             have r₂ := b2e482092 y
             grind)
          | exact resolve b2e482095 b2e482092
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482092 b2e482095
        have b2e482220 : (τ (σ y)) = (k y (τ y)) ∨ y = (k y (τ y)) := by
          first
          | (have i₁ := b2e127 y y
             have i₂ := b2e482107
             grind)
          | exact superpose b2e482107 b2e127
          | exact resolve b2e127 b2e482107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e127 b2e482107
        have b2e482293 : y = (k y (τ y)) ∨ y = (k y (τ y)) := by
          first
          | (have i₁ := b2e482220
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e482220
          | exact resolve b2e482220 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482220
        have b2e482294 : y = (k y (τ y)) := by grind
        clear b2e482293
        have b2e482329 : (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e27 y y
             have i₂ := b2e482294
             grind)
          | exact superpose b2e482294 b2e27
          | exact resolve b2e27 b2e482294
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482294
        have b2e485002 : (k (σ x) y) = (σ (M.op y (τ y))) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b2e482042 x
             have i₂ := b2e41 (τ y)
             grind)
          | exact superpose b2e41 b2e482042
          | (have j0 := b2e482042 x
             grind)
          | exact resolve b2e482042 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482042
        have b2e485849 : (k (σ y) y) = (k (σ x) y) ∨ x = (k x (τ y)) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e485002
             have i₂ := b2e413680 y
             grind)
          | exact superpose b2e413680 b2e485002
          | (have j1 := b2e413680 y
             grind)
          | exact resolve b2e485002 b2e413680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e413680 b2e485002
        have b2e485904 : (k (σ y) y) = (k (σ x) y) ∨ x = (k x (τ y)) := by
          first
          | (have j1 := b2e54 (τ y)
             grind)
          | (have r₁ := b2e485849
             have r₂ := b2e54 (τ y)
             grind)
          | exact resolve b2e485849 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e485849
        have b2e485906 : (σ y) = (k (σ x) y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b2e485904
             have i₂ := b2e482329
             grind)
          | exact superpose b2e482329 b2e485904
          | exact resolve b2e485904 b2e482329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e485904
        have b2e485985 : (σ y) = (M.op (σ x) y) ∨ (σ x) = (σ y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b2e478276 (σ x)
             have i₂ := b2e485906
             grind)
          | exact superpose b2e485906 b2e478276
          | exact resolve b2e478276 b2e485906
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e485906
        have b2e486015 : x = (k x (τ y)) ∨ (σ y) = (M.op (σ x) y) := by
          first
          | (have r₁ := b2e485985
             have r₂ := b2e460
             grind)
          | exact resolve b2e485985 b2e460
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e485985
        have b2e486216 : (σ x) = (k (σ x) y) ∨ (σ y) = (M.op (σ x) y) := by
          first
          | (have i₁ := b2e27 y x
             have i₂ := b2e486015
             grind)
          | exact superpose b2e486015 b2e27
          | exact resolve b2e27 b2e486015
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486015
        have b2e486566 : (σ x) = (k (σ y) y) ∨ (τ y) = (M.op y (τ y)) ∨ (σ y) = (M.op (σ x) y) := by
          first
          | (have i₁ := b2e437715
             have i₂ := b2e486216
             grind)
          | exact superpose b2e486216 b2e437715
          | exact resolve b2e437715 b2e486216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e437715 b2e486216
        have b2e486643 : (σ x) = (σ y) ∨ (τ y) = (M.op y (τ y)) ∨ (σ y) = (M.op (σ x) y) := by
          first
          | (have i₁ := b2e486566
             have i₂ := b2e482329
             grind)
          | exact superpose b2e482329 b2e486566
          | exact resolve b2e486566 b2e482329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482329 b2e486566
        have b2e486648 : (σ y) = (M.op (σ x) y) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have r₁ := b2e486643
             have r₂ := b2e460
             grind)
          | exact resolve b2e486643 b2e460
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486643
        have b2e486838 : (σ y) = (k (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e281 (σ x) y
             have i₂ := b2e486648
             grind)
          | exact superpose b2e486648 b2e281
          | exact resolve b2e281 b2e486648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486648
        have b2e486887 : (σ y) = (k (M.op (σ x) (σ x)) (σ y)) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have r₁ := b2e486838
             have r₂ := b2e21
             grind)
          | exact resolve b2e486838 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486838
        have b2e486909 : (σ y) = (k (σ x) (σ y)) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e486887
             have i₂ := b2e778
             grind)
          | exact superpose b2e778 b2e486887
          | exact resolve b2e486887 b2e778
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486887
        have b2e486918 : (σ y) = (σ (k x y)) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e486909
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e486909
          | exact resolve b2e486909 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486909
        have b2e486919 : (σ x) = (σ y) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e486918
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e486918
          | exact resolve b2e486918 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486918
        have b2e486920 : (τ y) = (M.op y (τ y)) := by
          first
          | (have r₁ := b2e486919
             have r₂ := b2e460
             grind)
          | exact resolve b2e486919 b2e460
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486919
        have b2e486939 : (τ y) ≠ (τ y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b2e54 (τ y)
             have i₂ := b2e486920
             grind)
          | exact superpose b2e486920 b2e54
          | (have j0 := b2e54 (τ y)
             grind)
          | (have r₁ := b2e54 (τ y)
             have r₂ := b2e486920
             grind)
          | exact resolve b2e54 b2e486920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e486940 : (τ y) = (k (τ y) y) := by
          first
          | (have i₁ := b2e168 (τ y)
             have i₂ := b2e486920
             grind)
          | exact superpose b2e486920 b2e168
          | exact resolve b2e168 b2e486920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e168
        have b2e486942 : (τ y) = (k (τ y) x) := by
          first
          | (have i₁ := b2e370 (τ y)
             have i₂ := b2e486920
             grind)
          | exact superpose b2e486920 b2e370
          | exact resolve b2e370 b2e486920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e486962 : ∀ X0 : G, (M.op y X0) = (M.op (τ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e37 y (τ y) X0
             have i₂ := b2e486920
             grind)
          | exact superpose b2e486920 b2e37
          | exact resolve b2e37 b2e486920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486920
        have b2e487039 : x = (k x (τ y)) := by grind
        clear b2e486939
        have b2e487123 : (σ x) = (k (σ x) y) := by
          first
          | (have i₁ := b2e27 y x
             have i₂ := b2e487039
             grind)
          | exact superpose b2e487039 b2e27
          | exact resolve b2e27 b2e487039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e487039
        have b2e487298 : (k y (σ y)) = (σ (τ y)) := by
          first
          | (have i₁ := b2e26 y y
             have i₂ := b2e486940
             grind)
          | exact superpose b2e486940 b2e26
          | exact resolve b2e26 b2e486940
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486940
        have b2e487434 : y = (k y (σ y)) := by
          first
          | (have i₁ := b2e487298
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e487298
          | exact resolve b2e487298 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e487298
        have b2e487574 : (σ y) = (M.op y (σ y)) ∨ y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e16030 y
             have i₂ := b2e487434
             grind)
          | exact superpose b2e487434 b2e16030
          | (have j0 := b2e16030 y
             grind)
          | exact resolve b2e16030 b2e487434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16030 b2e487434
        have b2e487701 : (k y (σ x)) = (σ (τ y)) := by
          first
          | (have i₁ := b2e26 y x
             have i₂ := b2e486942
             grind)
          | exact superpose b2e486942 b2e26
          | exact resolve b2e26 b2e486942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e486942
        have b2e487859 : y = (k y (σ x)) := by
          first
          | (have i₁ := b2e487701
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e487701
          | exact resolve b2e487701 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e487701
        have b2e488021 : x ≠ y ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e41357
             have i₂ := b2e487859
             grind)
          | exact superpose b2e487859 b2e41357
          | exact resolve b2e41357 b2e487859
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41357
        have b2e488034 : (σ x) = (M.op y (σ x)) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e16031 y
             have i₂ := b2e487859
             grind)
          | exact superpose b2e487859 b2e16031
          | (have j0 := b2e16031 y
             grind)
          | exact resolve b2e16031 b2e487859
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16031 b2e487859
        have b2e488210 : y ≠ (σ x) ∨ y = (M.op (σ x) y) := by
          first
          | (have i₁ := b2e448753 (σ x)
             have i₂ := b2e487123
             grind)
          | exact superpose b2e487123 b2e448753
          | (have j0 := b2e448753 (σ x)
             grind)
          | exact resolve b2e448753 b2e487123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e487123
        have b2e488467 : (M.op y (τ x)) = (τ (k y x)) ∨ (τ x) = (M.op y (τ x)) := by
          first
          | (have i₁ := b2e414113 y
             have i₂ := b2e486962 (τ x)
             grind)
          | exact superpose b2e486962 b2e414113
          | exact resolve b2e414113 b2e486962
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e414113 b2e486962
        have b2e488990 : (τ x) = (M.op y (τ x)) ∨ (τ y) = (M.op y (τ x)) := by
          first
          | (have i₁ := b2e488467
             have i₂ := b2e385
             grind)
          | exact superpose b2e385 b2e488467
          | exact resolve b2e488467 b2e385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e488467
        have b2e490195 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ y = (M.op y (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e37 y (σ y) X0
             have i₂ := b2e487574
             grind)
          | exact superpose b2e487574 b2e37
          | exact resolve b2e37 b2e487574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e490244 : y ≠ (σ y) ∨ y = (M.op y (σ y)) := by grind
        clear b2e487574
        have b2e490705 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) ∨ y = (M.op y (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e37 y (σ x) X0
             have i₂ := b2e488034
             grind)
          | exact superpose b2e488034 b2e37
          | exact resolve b2e37 b2e488034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e490755 : y ≠ (σ x) ∨ y = (M.op y (σ x)) := by grind
        have b2e492019 : (τ x) = (k (τ x) x) ∨ (τ y) = (M.op y (τ x)) := by
          first
          | (have i₁ := b2e370 (τ x)
             have i₂ := b2e488990
             grind)
          | exact superpose b2e488990 b2e370
          | exact resolve b2e370 b2e488990
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e370
        have b2e492093 : (τ x) ≠ (τ y) ∨ (τ y) = (M.op y (τ x)) := by grind
        clear b2e488990
        have b2e495494 : (σ (k y x)) = (M.op y (σ x)) ∨ y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e248
             have i₂ := b2e490195 (σ x)
             grind)
          | exact superpose b2e490195 b2e248
          | exact resolve b2e248 b2e490195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e248
        have b2e495495 : (σ x) ≠ (M.op y (σ x)) ∨ y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e490195 (σ x)
             grind)
          | exact superpose b2e490195 b2e22
          | exact resolve b2e22 b2e490195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e490195
        have b2e495752 : (σ y) = (M.op y (σ x)) ∨ y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e495494
             have i₂ := b2e385
             grind)
          | exact superpose b2e385 b2e495494
          | exact resolve b2e495494 b2e385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e385 b2e495494
        have b2e495775 : (σ x) ≠ (σ x) ∨ y = (M.op y (σ y)) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e495495
             have i₂ := b2e488034
             grind)
          | exact superpose b2e488034 b2e495495
          | (have r₁ := b2e495495
             have r₂ := b2e488034
             grind)
          | exact resolve b2e495495 b2e488034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e488034 b2e495495
        have b2e495782 : y = (M.op y (σ x)) ∨ y = (M.op y (σ y)) := by grind
        clear b2e495775
        have b2e495935 : y = (σ y) ∨ y = (M.op y (σ y)) ∨ y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e495782
             have i₂ := b2e495752
             grind)
          | exact superpose b2e495752 b2e495782
          | exact resolve b2e495782 b2e495752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e495752 b2e495782
        have b2e496029 : y = (σ y) ∨ y = (M.op y (σ y)) := by grind
        clear b2e495935
        have b2e496050 : y = (M.op y (σ y)) := by
          first
          | (have r₁ := b2e496029
             have r₂ := b2e490244
             grind)
          | exact resolve b2e496029 b2e490244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e490244 b2e496029
        have b2e496076 : (τ y) = (k (τ x) y) ∨ y = (σ y) := by
          first
          | (have i₁ := b2e35163
             have i₂ := b2e496050
             grind)
          | exact superpose b2e496050 b2e35163
          | exact resolve b2e35163 b2e496050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35163
        have b2e498280 : (σ x) = (M.op y (σ y)) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e18279
             have i₂ := b2e490705 (σ y)
             grind)
          | exact superpose b2e490705 b2e18279
          | exact resolve b2e18279 b2e490705
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18279 b2e490705
        have b2e498538 : y = (σ x) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e498280
             have i₂ := b2e496050
             grind)
          | exact superpose b2e496050 b2e498280
          | exact resolve b2e498280 b2e496050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e496050 b2e498280
        have b2e498556 : y = (M.op y (σ x)) := by
          first
          | (have r₁ := b2e498538
             have r₂ := b2e490755
             grind)
          | exact resolve b2e498538 b2e490755
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e490755 b2e498538
        have b2e498585 : (τ y) = (k (τ x) x) ∨ y = (σ x) := by
          first
          | (have i₁ := b2e39759
             have i₂ := b2e498556
             grind)
          | exact superpose b2e498556 b2e39759
          | exact resolve b2e39759 b2e498556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39759
        have b2e498593 : y ≠ (σ x) ∨ x = (M.op (σ x) x) ∨ x = (k (σ x) x) := by
          first
          | (have i₁ := b2e52 (σ x)
             have i₂ := b2e498556
             grind)
          | exact superpose b2e498556 b2e52
          | (have j0 := b2e52 (σ x)
             grind)
          | exact resolve b2e52 b2e498556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e498768 : y ≠ (σ x) ∨ x = (M.op (σ x) x) := by
          first
          | (have j1 := b2e448793 (σ x)
             grind)
          | (have r₁ := b2e498593
             have r₂ := b2e448793 (σ x)
             grind)
          | exact resolve b2e498593 b2e448793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e448793 b2e498593
        have b2e498810 : (τ x) = (τ y) ∨ (τ y) = (M.op y (τ x)) ∨ y = (σ x) := by
          first
          | (have i₁ := b2e492019
             have i₂ := b2e498585
             grind)
          | exact superpose b2e498585 b2e492019
          | exact resolve b2e492019 b2e498585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e492019 b2e498585
        have b2e498936 : (τ y) = (M.op y (τ x)) ∨ y = (σ x) := by
          first
          | (have r₁ := b2e498810
             have r₂ := b2e492093
             grind)
          | exact resolve b2e498810 b2e492093
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e492093 b2e498810
        have b2e499159 : (σ (τ y)) = (k (σ x) x) ∨ (τ x) = (τ y) ∨ y = (σ x) := by
          first
          | (have i₁ := b2e430719
             have i₂ := b2e498936
             grind)
          | exact superpose b2e498936 b2e430719
          | exact resolve b2e430719 b2e498936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e430719 b2e498936
        have b2e499298 : y = (k (σ x) x) ∨ (τ x) = (τ y) ∨ y = (σ x) := by
          first
          | (have i₁ := b2e499159
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e499159
          | exact resolve b2e499159 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e499159
        have b2e504054 : y = (M.op (σ x) x) ∨ y = (σ x) ∨ (τ x) = (τ y) ∨ y = (σ x) := by
          first
          | (have i₁ := b2e478314 (σ x)
             have i₂ := b2e499298
             grind)
          | exact superpose b2e499298 b2e478314
          | exact resolve b2e478314 b2e499298
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478314 b2e499298
        have b2e504064 : y = (M.op (σ x) x) ∨ y = (σ x) ∨ (τ x) = (τ y) := by grind
        clear b2e504054
        have b2e504319 : y = (k (M.op (σ x) (σ x)) y) ∨ y = (M.op (σ x) y) ∨ y = (σ x) ∨ (τ x) = (τ y) := by
          first
          | (have i₁ := b2e281 (σ x) x
             have i₂ := b2e504064
             grind)
          | exact superpose b2e504064 b2e281
          | exact resolve b2e281 b2e504064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e281 b2e504064
        have b2e504361 : y = (k (M.op (σ x) (σ x)) y) ∨ y = (M.op (σ x) y) ∨ (τ x) = (τ y) := by
          first
          | (have r₁ := b2e504319
             have r₂ := b2e488210
             grind)
          | exact resolve b2e504319 b2e488210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e488210 b2e504319
        have b2e504373 : y = (k (σ x) y) ∨ y = (M.op (σ x) y) ∨ (τ x) = (τ y) := by
          first
          | (have i₁ := b2e504361
             have i₂ := b2e778
             grind)
          | exact superpose b2e778 b2e504361
          | exact resolve b2e504361 b2e778
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e778 b2e504361
        have b2e504382 : y = (M.op (σ x) y) ∨ (τ x) = (τ y) := by
          first
          | (have j1 := b2e448753 (σ x)
             grind)
          | (have r₁ := b2e504373
             have r₂ := b2e448753 (σ x)
             grind)
          | exact resolve b2e504373 b2e448753
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e448753 b2e504373
        have b2e504442 : y ≠ y ∨ (σ x) = (M.op y (σ x)) ∨ (σ x) = (k y (σ x)) ∨ (τ x) = (τ y) := by
          first
          | (have i₁ := b2e16 y (σ x)
             have i₂ := b2e504382
             grind)
          | exact superpose b2e504382 b2e16
          | (have j0 := b2e16 y (σ x)
             grind)
          | (have r₁ := b2e16 y (σ x)
             have r₂ := b2e504382
             grind)
          | exact resolve b2e16 b2e504382
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504382
        have b2e504496 : (σ x) = (M.op y (σ x)) ∨ (σ x) = (k y (σ x)) ∨ (τ x) = (τ y) := by grind
        clear b2e504442
        have b2e504509 : (σ x) = (M.op y (σ x)) ∨ (τ x) = (τ y) := by
          first
          | (have j1 := b2e29068 y
             grind)
          | (have r₁ := b2e504496
             have r₂ := b2e29068 y
             grind)
          | exact resolve b2e504496 b2e29068
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504496
        have b2e504517 : (τ x) = (τ y) ∨ y = (σ x) := by
          first
          | (have i₁ := b2e504509
             have i₂ := b2e498556
             grind)
          | exact superpose b2e498556 b2e504509
          | exact resolve b2e504509 b2e498556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504509
        have b2e504662 : x = (σ (τ y)) ∨ y = (σ x) := by
          first
          | (have i₁ := b2e14 x
             have i₂ := b2e504517
             grind)
          | exact superpose b2e504517 b2e14
          | exact resolve b2e14 b2e504517
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504517
        have b2e504865 : y = (σ x) ∨ x = y := by
          first
          | (have i₁ := b2e504662
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e504662
          | exact resolve b2e504662 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504662
        have b2e505054 : x = (τ y) ∨ x = y := by
          first
          | (have i₁ := b2e13 x
             have i₂ := b2e504865
             grind)
          | exact superpose b2e504865 b2e13
          | exact resolve b2e13 b2e504865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504865
        have b2e505359 : (k x (σ x)) = (σ (k (k x x) x)) ∨ x = (k x (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e338856
             have i₂ := b2e505054
             grind)
          | exact superpose b2e505054 b2e338856
          | exact resolve b2e338856 b2e505054
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e338856 b2e505054
        have b2e505622 : (k x (σ x)) = (σ (k (k x x) x)) ∨ x = (k x (σ x)) := by
          first
          | (have r₁ := b2e505359
             have r₂ := b2e488021
             grind)
          | exact resolve b2e505359 b2e488021
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e488021 b2e505359
        have b2e505659 : (σ (k x x)) = (k x (σ x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e505622
             have i₂ := b2e557
             grind)
          | exact superpose b2e557 b2e505622
          | exact resolve b2e505622 b2e557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e505622
        have b2e505684 : (σ x) = (k x (σ x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e505659
             have i₂ := b2e557
             grind)
          | exact superpose b2e557 b2e505659
          | exact resolve b2e505659 b2e557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e505659
        have b2e505690 : x = (k x (σ x)) := by
          first
          | (have j1 := b2e27345 x
             grind)
          | (have r₁ := b2e505684
             have r₂ := b2e27345 x
             grind)
          | exact resolve b2e505684 b2e27345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27345 b2e505684
        have b2e505726 : (σ x) = (σ (M.op y (σ x))) ∨ x = (M.op (σ x) x) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e11685 (σ x)
             have i₂ := b2e505690
             grind)
          | exact superpose b2e505690 b2e11685
          | (have j0 := b2e11685 (σ x)
             grind)
          | exact resolve b2e11685 b2e505690
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11685 b2e505690
        have b2e505843 : (σ x) = (σ y) ∨ x = (M.op (σ x) x) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e505726
             have i₂ := b2e498556
             grind)
          | exact superpose b2e498556 b2e505726
          | exact resolve b2e505726 b2e498556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e505726
        have b2e505883 : x = (M.op (σ x) x) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have r₁ := b2e505843
             have r₂ := b2e460
             grind)
          | exact resolve b2e505843 b2e460
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e505843
        have b2e505916 : y = (σ x) ∨ x = (M.op (σ x) x) := by
          first
          | (have i₁ := b2e505883
             have i₂ := b2e498556
             grind)
          | exact superpose b2e498556 b2e505883
          | exact resolve b2e505883 b2e498556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e505883
        have b2e505939 : x = (M.op (σ x) x) := by
          first
          | (have r₁ := b2e505916
             have r₂ := b2e498768
             grind)
          | exact resolve b2e505916 b2e498768
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e498768 b2e505916
        have b2e505989 : x ≠ (τ x) ∨ x = (M.op (τ x) x) := by
          first
          | (have i₁ := b2e449604 x
             have i₂ := b2e505939
             grind)
          | exact superpose b2e505939 b2e449604
          | exact resolve b2e449604 b2e505939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e449604
        have b2e506047 : x ≠ x ∨ (σ x) = (M.op x (σ x)) ∨ (σ x) = (k x (σ x)) := by
          first
          | (have i₁ := b2e16 x (σ x)
             have i₂ := b2e505939
             grind)
          | exact superpose b2e505939 b2e16
          | (have j0 := b2e16 x (σ x)
             grind)
          | (have r₁ := b2e16 x (σ x)
             have r₂ := b2e505939
             grind)
          | exact resolve b2e16 b2e505939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e505939
        have b2e506116 : (σ x) = (M.op x (σ x)) ∨ (σ x) = (k x (σ x)) := by grind
        clear b2e506047
        have b2e506145 : (σ x) = (M.op x (σ x)) := by
          first
          | (have j1 := b2e29068 x
             grind)
          | (have r₁ := b2e506116
             have r₂ := b2e29068 x
             grind)
          | exact resolve b2e506116 b2e29068
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29068 b2e506116
        have b2e506165 : (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e506145
             have i₂ := b2e41 (σ x)
             grind)
          | exact superpose b2e41 b2e506145
          | exact resolve b2e506145 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e506145
        have b2e506176 : y = (σ x) := by
          first
          | (have i₁ := b2e506165
             have i₂ := b2e498556
             grind)
          | exact superpose b2e498556 b2e506165
          | exact resolve b2e506165 b2e498556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e498556 b2e506165
        have b2e506193 : y ≠ (σ y) := by
          first
          | (have i₁ := b2e460
             have i₂ := b2e506176
             grind)
          | exact superpose b2e506176 b2e460
          | exact resolve b2e460 b2e506176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e460
        have b2e506333 : x = (τ y) := by
          first
          | (have i₁ := b2e13 x
             have i₂ := b2e506176
             grind)
          | exact superpose b2e506176 b2e13
          | exact resolve b2e13 b2e506176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e506340 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e31 X0 x
             have i₂ := b2e506176
             grind)
          | exact superpose b2e506176 b2e31
          | exact resolve b2e31 b2e506176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e511395 : (τ (τ y)) = (k (τ (τ x)) x) ∨ y = (σ y) := by
          first
          | (have i₁ := b2e506340 (τ x)
             have i₂ := b2e496076
             grind)
          | exact superpose b2e496076 b2e506340
          | exact resolve b2e506340 b2e496076
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e496076 b2e506340
        have b2e511754 : (τ (τ y)) = (k (τ (τ x)) x) := by
          first
          | (have r₁ := b2e511395
             have r₂ := b2e506193
             grind)
          | exact resolve b2e511395 b2e506193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e511395
        have b2e511812 : (τ x) = (k (τ (τ x)) x) := by
          first
          | (have i₁ := b2e511754
             have i₂ := b2e506333
             grind)
          | exact superpose b2e506333 b2e511754
          | exact resolve b2e511754 b2e506333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e506333 b2e511754
        have b2e511873 : (σ (τ x)) = (k (τ x) (σ x)) := by
          first
          | (have i₁ := b2e26 (τ x) x
             have i₂ := b2e511812
             grind)
          | exact superpose b2e511812 b2e26
          | exact resolve b2e26 b2e511812
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e511890 : (σ x) ≠ (σ (τ x)) ∨ (σ (τ x)) = (σ (τ (τ x))) := by
          first
          | (have i₁ := b2e26909 (τ (τ x))
             have i₂ := b2e511812
             grind)
          | exact superpose b2e511812 b2e26909
          | exact resolve b2e26909 b2e511812
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26909 b2e511812
        have b2e511975 : x ≠ (σ x) ∨ (σ (τ x)) = (σ (τ (τ x))) := by
          first
          | (have i₁ := b2e511890
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e511890
          | exact resolve b2e511890 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e511890
        have b2e511989 : (σ (τ x)) = (k (τ x) y) := by
          first
          | (have i₁ := b2e511873
             have i₂ := b2e506176
             grind)
          | exact superpose b2e506176 b2e511873
          | exact resolve b2e511873 b2e506176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e511873
        have b2e512002 : x ≠ y ∨ (σ (τ x)) = (σ (τ (τ x))) := by
          first
          | (have i₁ := b2e511975
             have i₂ := b2e506176
             grind)
          | exact superpose b2e506176 b2e511975
          | exact resolve b2e511975 b2e506176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e511975
        have b2e512016 : x = (k (τ x) y) := by
          first
          | (have i₁ := b2e511989
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e511989
          | exact resolve b2e511989 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e511989
        have b2e512023 : (τ x) = (σ (τ x)) ∨ x ≠ y := by
          first
          | (have i₁ := b2e512002
             have i₂ := b2e14 (τ x)
             grind)
          | exact superpose b2e14 b2e512002
          | exact resolve b2e512002 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e512002
        have b2e512042 : x ≠ y ∨ x = (τ x) := by
          first
          | (have i₁ := b2e512023
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e512023
          | exact resolve b2e512023 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e512023
        have b2e512306 : x = (M.op (τ x) y) ∨ x = (τ x) := by
          first
          | (have i₁ := b2e478276 (τ x)
             have i₂ := b2e512016
             grind)
          | exact superpose b2e512016 b2e478276
          | exact resolve b2e478276 b2e512016
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478276
        have b2e514756 : (k x x) = (M.op (τ x) x) ∨ x = (M.op (τ x) x) ∨ x = (τ x) := by
          first
          | (have i₁ := b2e481420 (τ x) y
             have i₂ := b2e512306
             grind)
          | exact superpose b2e512306 b2e481420
          | (have j0 := b2e481420 (τ x) x
             grind)
          | exact resolve b2e481420 b2e512306
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e481420 b2e512306
        have b2e514759 : (k x x) = (M.op (τ x) x) ∨ x = (M.op (τ x) x) := by
          first
          | (have r₁ := b2e514756
             have r₂ := b2e505989
             grind)
          | exact resolve b2e514756 b2e505989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e505989 b2e514756
        have b2e514785 : x = (M.op (τ x) x) ∨ x = (M.op (τ x) x) := by
          first
          | (have i₁ := b2e514759
             have i₂ := b2e557
             grind)
          | exact superpose b2e557 b2e514759
          | exact resolve b2e514759 b2e557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e557 b2e514759
        have b2e514786 : x = (M.op (τ x) x) := by grind
        clear b2e514785
        have b2e514829 : (k x y) = (M.op (τ x) y) ∨ (τ x) = (k (τ x) y) := by
          first
          | (have i₁ := b2e446380 x
             have i₂ := b2e514786
             grind)
          | exact superpose b2e514786 b2e446380
          | exact resolve b2e446380 b2e514786
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e446380
        have b2e514870 : ∀ X0 : G, (M.op x X0) = (M.op (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e37 (τ x) x X0
             have i₂ := b2e514786
             grind)
          | exact superpose b2e514786 b2e37
          | exact resolve b2e37 b2e514786
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e514786
        have b2e514961 : ∀ X0 : G, (M.op y X0) = (M.op (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e514870 X0
             have i₂ := b2e41 X0
             grind)
          | exact superpose b2e41 b2e514870
          | exact resolve b2e514870 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e514870
        have b2e514970 : x = (M.op (τ x) y) ∨ (τ x) = (k (τ x) y) := by
          first
          | (have i₁ := b2e514829
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e514829
          | exact resolve b2e514829 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e514829
        have b2e514988 : x = (M.op y y) ∨ (τ x) = (k (τ x) y) := by
          first
          | (have i₁ := b2e514970
             have i₂ := b2e514961 y
             grind)
          | exact superpose b2e514961 b2e514970
          | exact resolve b2e514970 b2e514961
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e514970
        have b2e514994 : x = y ∨ (τ x) = (k (τ x) y) := by
          first
          | (have i₁ := b2e514988
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e514988
          | exact resolve b2e514988 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e514988
        have b2e514997 : x = (τ x) ∨ x = y := by
          first
          | (have i₁ := b2e514994
             have i₂ := b2e512016
             grind)
          | exact superpose b2e512016 b2e514994
          | exact resolve b2e514994 b2e512016
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e512016 b2e514994
        have b2e514998 : x = (τ x) := by
          first
          | (have r₁ := b2e514997
             have r₂ := b2e512042
             grind)
          | exact resolve b2e514997 b2e512042
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e512042 b2e514997
        have b2e515151 : x = (σ x) := by
          first
          | (have i₁ := b2e14 x
             have i₂ := b2e514998
             grind)
          | exact superpose b2e514998 b2e14
          | exact resolve b2e14 b2e514998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e515152 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e26 x X0
             have i₂ := b2e514998
             grind)
          | exact superpose b2e514998 b2e26
          | exact resolve b2e26 b2e514998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e515252 : ∀ X0 : G, x = (k x (σ (σ (M.op (τ x) (M.op (τ x) X0))))) := by
          intro X0
          first
          | (have i₁ := b2e5429 x x
             have i₂ := b2e514998
             grind)
          | exact superpose b2e514998 b2e5429
          | exact resolve b2e5429 b2e514998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5429 b2e514998
        have b2e515393 : ∀ X0 : G, x = (k x (σ (σ (M.op y (M.op (τ x) X0))))) := by
          intro X0
          first
          | (have i₁ := b2e515252 X0
             have i₂ := b2e514961 (M.op (τ x) X0)
             grind)
          | exact superpose b2e514961 b2e515252
          | exact resolve b2e515252 b2e514961
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e515252
        have b2e515407 : x = y := by
          first
          | (have i₁ := b2e515151
             have i₂ := b2e506176
             grind)
          | exact superpose b2e506176 b2e515151
          | exact resolve b2e515151 b2e506176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e515151
        have b2e515477 : ∀ X0 : G, x = (σ (k x (σ (M.op y (M.op (τ x) X0))))) := by
          intro X0
          first
          | (have i₁ := b2e515393 X0
             have i₂ := b2e515152 (σ (M.op y (M.op (τ x) X0)))
             grind)
          | exact superpose b2e515152 b2e515393
          | exact resolve b2e515393 b2e515152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e515393
        have b2e515531 : ∀ X0 : G, x = (σ (σ (k x (M.op y (M.op (τ x) X0))))) := by
          intro X0
          first
          | (have i₁ := b2e515477 X0
             have i₂ := b2e515152 (M.op y (M.op (τ x) X0))
             grind)
          | exact superpose b2e515152 b2e515477
          | exact resolve b2e515477 b2e515152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e515152 b2e515477
        have b2e515569 : ∀ X0 : G, x = (σ (σ (k x (M.op y (M.op y X0))))) := by
          intro X0
          first
          | (have i₁ := b2e515531 X0
             have i₂ := b2e514961 X0
             grind)
          | exact superpose b2e514961 b2e515531
          | exact resolve b2e515531 b2e514961
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e514961 b2e515531
        have b2e515599 : x = (σ (σ x)) := by
          first
          | (have i₁ := b2e515569 x
             have i₂ := b2e1493 x
             grind)
          | exact superpose b2e1493 b2e515569
          | exact resolve b2e515569 b2e1493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1493 b2e515569
        have b2e515617 : x = (σ y) := by
          first
          | (have i₁ := b2e515599
             have i₂ := b2e506176
             grind)
          | exact superpose b2e506176 b2e515599
          | exact resolve b2e515599 b2e506176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e506176 b2e515599
        have b2e515625 : y = (σ y) := by
          first
          | (have i₁ := b2e515617
             have i₂ := b2e515407
             grind)
          | exact superpose b2e515407 b2e515617
          | exact resolve b2e515617 b2e515407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e515407 b2e515617
        have b2e515628 : False := by grind
        exact b2e515628
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
        have b3e40 : (k x y) = (τ (σ x)) := by
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
        have b3e41 : x = (k x y) := by
          first
          | (have i₁ := b3e40
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e40
          | exact resolve b3e40 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e44 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) := by
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
        have b3e48 : y = (M.op x y) ∨ y = (k x y) := by grind
        clear b3e44
        have b3e51 : y = (k x y) := by
          first
          | (have r₁ := b3e48
             have r₂ := b3e20
             grind)
          | exact resolve b3e48 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e65 : x = y := by
          first
          | (have i₁ := b3e51
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e51
          | exact resolve b3e51 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e51
        have b3e77 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e20
          | exact resolve b3e20 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e78 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e21
          | exact resolve b3e21 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e86 : False := by grind
        exact b3e86
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
          have b4e36 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X0 X2) X3 (M.op X1 X1)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X0 X0) X2
               have i₂ := b4e13 X0 X0 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 (M.op X0 X2) (M.op X1 X1)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X0 X2) (M.op X1 X1)
               grind)
            | (have r₁ := b4e16 (M.op X0 X2) (M.op X0 X0)
               have r₂ := b4e13 X0 X0 X2
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 X0 X1 x
               have i₂ := b4e13 X1 X0 x
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e42 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e38 X0 x X2 X3
               have i₂ := b4e13 X0 X3 x
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e44 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X1 (M.op X0 X0)
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e46 : ∀ X1 : G, (M.op x X1) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b4e44 x X1
               have i₂ := b4e13 y X1 x
               grind)
            | exact superpose b4e13 b4e44
            | exact resolve b4e44 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e83 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) X0) = X0 ∨ (k (M.op X1 X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (M.op X1 X1) X0
               have i₂ := b4e41 X1 X0
               grind)
            | exact superpose b4e41 b4e17
            | (have j0 := b4e17 (M.op X1 X1) X0
               grind)
            | (have r₁ := b4e17 (M.op X1 X1) X1
               have r₂ := b4e41 X1 X1
               grind)
            | exact resolve b4e17 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e93 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k (M.op X1 X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e83 X0 X1
               have i₂ := b4e42 X1 X1 X0
               grind)
            | exact superpose b4e42 b4e83
            | (have j0 := b4e83 X0 X1
               grind)
            | (have r₁ := b4e83 (M.op X0 x) X0
               have r₂ := b4e42 X0 x X0
               grind)
            | (have r₁ := b4e83 X0 (M.op X0 x)
               have r₂ := b4e42 X0 x (M.op X0 x)
               grind)
            | exact resolve b4e83 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83
          have b4e102 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
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
          have b4e196 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e40 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e248 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 (σ X0) X1
               have i₂ := b4e63 X0 X0
               grind)
            | exact superpose b4e63 b4e41
            | (have j1 := b4e63 X0 X0
               grind)
            | exact resolve b4e41 b4e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e257 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e63 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e259 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e257 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257
          have b4e265 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e248 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e248
          have b4e447 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e196 y X0
               have i₂ := b4e46 y
               grind)
            | exact superpose b4e46 b4e196
            | exact resolve b4e196 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e196
          have b4e451 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e447 x
               have i₂ := b4e46 x
               grind)
            | exact superpose b4e46 b4e447
            | exact resolve b4e447 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e447
          have b4e914 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e259 X0
               have i₂ := b4e18 X0 X0
               grind)
            | exact superpose b4e18 b4e259
            | (have j0 := b4e259 X0
               have j1 := b4e18 (σ X0) (σ X0)
               grind)
            | exact resolve b4e259 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e916 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e259 (M.op x y)
               have i₂ := b4e451 y
               grind)
            | exact superpose b4e451 b4e259
            | (have j0 := b4e259 (M.op x y)
               grind)
            | exact resolve b4e259 b4e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e259 b4e451
          have b4e923 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
          clear b4e916
          have b4e925 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e914 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e914
          have b4e1011 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e93 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e1138 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e265 X0 X1
               have i₂ := b4e18 X0 X0
               grind)
            | exact superpose b4e18 b4e265
            | (have j0 := b4e265 X0 X1
               have j1 := b4e18 (σ X0) (σ X0)
               grind)
            | exact resolve b4e265 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e265
          have b4e1180 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e1138 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1138
          have b4e1206 : y = (k (M.op x y) y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e1011 y
               have i₂ := b4e46 y
               grind)
            | exact superpose b4e46 b4e1011
            | exact resolve b4e1011 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1011
          have b4e1224 : y = (k (M.op x y) y) := by
            first
            | (have r₁ := b4e1206
               have r₂ := b4e21
               grind)
            | exact resolve b4e1206 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1206
          have b4e9727 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e925 y
               have i₂ := b4e46 y
               grind)
            | exact superpose b4e46 b4e925
            | (have j0 := b4e925 y
               grind)
            | exact resolve b4e925 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e925
          have b4e9738 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b4e9727
               have r₂ := b4e21
               grind)
            | exact resolve b4e9727 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9727
          have b4e9745 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e9738
               have i₂ := b4e102 (σ y)
               grind)
            | exact superpose b4e102 b4e9738
            | exact resolve b4e9738 b4e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9738
          have b4e9746 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have r₁ := b4e9745
               have r₂ := b4e23
               grind)
            | exact resolve b4e9745 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9745
          have b4e15541 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e1180 y x
               have i₂ := b4e46 y
               grind)
            | exact superpose b4e46 b4e1180
            | (have j0 := b4e1180 y x
               grind)
            | exact resolve b4e1180 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e1180
          have b4e15689 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have j0 := b4e15541 X0
               grind)
            | (have r₁ := b4e15541 X0
               have r₂ := b4e21
               grind)
            | exact resolve b4e15541 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15541
          have b4e15697 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b4e15689 X0
               have i₂ := b4e102 (σ y)
               grind)
            | exact superpose b4e102 b4e15689
            | (have j0 := b4e15689 X0
               grind)
            | exact resolve b4e15689 b4e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15689
          have b4e15698 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
            intro X0
            first
            | (have j0 := b4e15697 X0
               grind)
            | (have r₁ := b4e15697 X0
               have r₂ := b4e23
               grind)
            | exact resolve b4e15697 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15697
          have b4e15774 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have i₁ := b4e923
               have i₂ := b4e15698 (σ (M.op x y))
               grind)
            | exact superpose b4e15698 b4e923
            | exact resolve b4e923 b4e15698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e923
          have b4e16054 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b4e63 (M.op x y) y
               have i₂ := b4e15774
               grind)
            | exact superpose b4e15774 b4e63
            | (have j0 := b4e63 (M.op x y) y
               grind)
            | exact resolve b4e63 b4e15774
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63 b4e15774
          have b4e16097 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
            first
            | (have r₁ := b4e16054
               have r₂ := b4e9746
               grind)
            | exact resolve b4e16054 b4e9746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16054
          have b4e16110 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e16097
               have i₂ := b4e1224
               grind)
            | exact superpose b4e1224 b4e16097
            | exact resolve b4e16097 b4e1224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1224 b4e16097
          have b4e16122 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
            first
            | (have r₁ := b4e16110
               have r₂ := b4e9746
               grind)
            | exact resolve b4e16110 b4e9746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9746 b4e16110
          have b4e16131 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e16122
               have i₂ := b4e102 (σ (M.op x y))
               grind)
            | exact superpose b4e102 b4e16122
            | exact resolve b4e16122 b4e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102 b4e16122
          have b4e16137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e16131
               have i₂ := b4e15698 (σ x)
               grind)
            | exact superpose b4e15698 b4e16131
            | exact resolve b4e16131 b4e15698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15698 b4e16131
          have b4e16140 : False := by grind
          exact b4e16140
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
          have b5e44 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) := by
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
          have b5e47 : y = (M.op x y) ∨ y = (k x y) := by grind
          clear b5e44
          have b5e50 : y = (k x y) := by
            first
            | (have r₁ := b5e47
               have r₂ := b5e21
               grind)
            | exact resolve b5e47 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e187 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e55 x y
               grind)
            | exact superpose b5e55 b5e24
            | (have j1 := b5e55 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e55 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e55 y x
               grind)
            | exact resolve b5e24 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e199 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e187
          have b5e209 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e199
               have r₂ := b5e23
               grind)
            | exact resolve b5e199 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e199
          have b5e217 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e209
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e209
            | exact resolve b5e209 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e209
          have b5e218 : False := by grind
          exact b5e218
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
        have b6e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b6e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X0 X2) X3 (M.op X1 X1)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 (M.op X0 X0) X2
             have i₂ := b6e12 X0 X0 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 (M.op X0 X2) (M.op X1 X1)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X0 X2) (M.op X1 X1)
             grind)
          | (have r₁ := b6e15 (M.op X0 X2) (M.op X0 X0)
             have r₂ := b6e12 X0 X0 X2
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e37 X0 X1 x
             have i₂ := b6e12 X1 X0 x
             grind)
          | exact superpose b6e12 b6e37
          | exact resolve b6e37 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e40 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b6e36 X0 x X2 X3
             have i₂ := b6e12 X0 X3 x
             grind)
          | exact superpose b6e12 b6e36
          | exact resolve b6e36 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e41 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
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
        have b6e42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (M.op (M.op X1 X1) (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 (M.op X1 X1) (M.op X0 X2)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e16
          | (have j0 := b6e16 (M.op X1 X1) (M.op X0 X2)
             grind)
          | (have r₁ := b6e16 (M.op X0 X0) (M.op X0 X2)
             have r₂ := b6e12 X0 X0 X2
             grind)
          | exact resolve b6e16 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b6e41
        have b6e44 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X2) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e42 X0 X1 X2
             have i₂ := b6e40 X1 X1 (M.op X0 X2)
             grind)
          | exact superpose b6e40 b6e42
          | (have j0 := b6e42 X0 X1 X2
             grind)
          | (have r₁ := b6e42 (M.op X0 X2) X0 X2
             have r₂ := b6e40 X0 X2 X0
             grind)
          | (have r₁ := b6e42 X0 (M.op X0 X2) X2
             have r₂ := b6e40 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b6e42 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e45 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e43
          | exact resolve b6e43 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 (M.op X1 X1)
             have i₂ := b6e39 X1 X0
             grind)
          | exact superpose b6e39 b6e15
          | (have j0 := b6e15 X0 (M.op X1 X1)
             grind)
          | (have r₁ := b6e15 X1 (M.op X1 X1)
             have r₂ := b6e39 X1 X1
             grind)
          | exact resolve b6e15 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e58 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
        have b6e61 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e58
             have r₂ := b6e21
             grind)
          | exact resolve b6e58 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e64 : x = (M.op x y) := by
          first
          | (have r₁ := b6e61
             have r₂ := b6e20
             grind)
          | exact resolve b6e61 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e66 : (σ x) ≠ (σ y) := by
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
        have b6e67 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e64
             grind)
          | exact superpose b6e64 b6e20
          | exact resolve b6e20 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e40 (σ x) (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e40
          | exact resolve b6e40 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e79 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X2) = (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X1 (M.op X0 X2)
             have i₂ := b6e40 X0 X2 X1
             grind)
          | exact superpose b6e40 b6e16
          | (have j0 := b6e16 X1 (M.op X0 X2)
             grind)
          | exact resolve b6e16 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e81 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X2) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 (M.op X0 X2) X1
             have i₂ := b6e40 X0 X2 X1
             grind)
          | exact superpose b6e40 b6e15
          | (have j0 := b6e15 X0 X1
             grind)
          | exact resolve b6e15 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e95 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e27 X0 X1
             grind)
          | exact superpose b6e27 b6e13
          | exact resolve b6e13 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e102 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e28 X1 X0
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e130 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e75 (σ y)
             grind)
          | exact superpose b6e75 b6e22
          | exact resolve b6e22 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e134 : ∀ X0 : G, (M.op (σ y) X0) ≠ X0 ∨ (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e75 X0
             grind)
          | exact superpose b6e75 b6e15
          | (have j0 := b6e15 (σ y) X0
             grind)
          | exact resolve b6e15 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e145 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e45
             grind)
          | exact superpose b6e45 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | (have r₁ := b6e15 (σ y) (σ x)
             have r₂ := b6e45
             grind)
          | exact resolve b6e15 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e146 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by grind
        clear b6e145
        have b6e148 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e146
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e146
          | exact resolve b6e146 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146
        have b6e151 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e130
             grind)
          | exact superpose b6e130 b6e15
          | (have j0 := b6e15 (σ y) (σ y)
             grind)
          | (have r₁ := b6e15 (σ y) (σ y)
             have r₂ := b6e130
             grind)
          | exact resolve b6e15 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e154 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b6e151
        have b6e155 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e154
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e154
          | exact resolve b6e154 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e154
        have b6e160 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k (M.op (σ y) X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e38 (σ y) (σ y) x
             have i₂ := b6e130
             grind)
          | exact superpose b6e130 b6e38
          | exact resolve b6e38 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e169 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (σ y)) := by
          intro X0
          first
          | (have j0 := b6e160 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e160
        have b6e186 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e155
             grind)
          | exact superpose b6e155 b6e13
          | exact resolve b6e13 b6e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e155
        have b6e188 : y = (k y y) := by
          first
          | (have i₁ := b6e186
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e186
          | exact resolve b6e186 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e186
        have b6e203 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ y) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e57 x x
             have i₂ := b6e75 (σ x)
             grind)
          | exact superpose b6e75 b6e57
          | (have j0 := b6e57 x X0
             grind)
          | exact resolve b6e57 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e230 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e75 (σ X0)
             have i₂ := b6e57 X0 x
             grind)
          | exact superpose b6e57 b6e75
          | (have j1 := b6e57 X0 x
             grind)
          | exact resolve b6e75 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e232 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op (σ X1) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e40 (σ X1) (σ X0) X2
             have i₂ := b6e57 X0 X1
             grind)
          | exact superpose b6e57 b6e40
          | (have j1 := b6e57 X0 X1
             grind)
          | exact resolve b6e40 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e233 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 (σ X0) (σ X1)
             have i₂ := b6e57 X0 X1
             grind)
          | exact superpose b6e57 b6e16
          | (have j0 := b6e16 (σ X0) (σ X1)
             have j1 := b6e57 X0 X1
             grind)
          | (have r₁ := b6e16 (σ X0) (σ X1)
             have r₂ := b6e57 X0 X1
             grind)
          | (have r₁ := b6e16 (σ X1) (σ X0)
             have r₂ := b6e57 X0 X1
             grind)
          | exact resolve b6e16 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e236 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e57 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e237 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e238 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e236 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e236
        have b6e240 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e233 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e233
        have b6e241 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e240 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e240
        have b6e251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e241 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e241
          | (have j0 := b6e241 X0 X1
             grind)
          | exact resolve b6e241 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e241
        have b6e284 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
        have b6e285 : y = (M.op y y) := by grind
        clear b6e284
        have b6e327 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (M.op y (M.op y X0)) ∨ (M.op y X0) = (k y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b6e44 y y x
             have i₂ := b6e285
             grind)
          | exact superpose b6e285 b6e44
          | (have j0 := b6e44 y y X0
             grind)
          | exact resolve b6e44 b6e285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e328 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b6e38 y y x
             have i₂ := b6e285
             grind)
          | exact superpose b6e285 b6e38
          | exact resolve b6e38 b6e285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e336 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) y) := by
          intro X0
          first
          | (have j0 := b6e328 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e328
        have b6e337 : ∀ X0 : G, (M.op y X0) = (k y (M.op y X0)) ∨ (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have j0 := b6e327 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e327
        have b6e338 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e95 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e95
          | exact resolve b6e95 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e525 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e50 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e558 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b6e102 X0 (M.op (σ X0) (σ X0))
             have i₂ := b6e525 (σ X0)
             grind)
          | exact superpose b6e525 b6e102
          | exact resolve b6e102 b6e525
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e525
        have b6e562 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e558 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e558
          | exact resolve b6e558 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e558
        have b6e596 : (τ (σ x)) = (k y x) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e148
             grind)
          | exact superpose b6e148 b6e13
          | exact resolve b6e13 b6e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e148
        have b6e614 : (σ y) = (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e596
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e596
          | exact resolve b6e596 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e596
        have b6e681 : x = (k x (τ (M.op (σ y) (σ x)))) := by
          first
          | (have i₁ := b6e562 x
             have i₂ := b6e75 (σ x)
             grind)
          | exact superpose b6e75 b6e562
          | exact resolve b6e562 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e562
        have b6e749 : x = (k x (τ (σ x))) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e681
             have i₂ := b6e45
             grind)
          | exact superpose b6e45 b6e681
          | exact resolve b6e681 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e681
        have b6e753 : (σ x) = (σ (k y x)) ∨ x = (k x x) := by
          first
          | (have i₁ := b6e749
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e749
          | exact resolve b6e749 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e749
        have b6e944 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e238 (τ X0)
             have i₂ := b6e27 X0 (τ X0)
             grind)
          | exact superpose b6e27 b6e238
          | (have j0 := b6e238 (τ X0)
             grind)
          | exact resolve b6e238 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e238
        have b6e950 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e944 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e944
          | (have j0 := b6e944 X0
             grind)
          | exact resolve b6e944 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e944
        have b6e953 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e950 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e950
          | (have j0 := b6e950 X0
             grind)
          | exact resolve b6e950 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e950
        have b6e960 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e953 (τ X0)
             have i₂ := b6e338 X0 X0
             grind)
          | exact superpose b6e338 b6e953
          | (have j0 := b6e953 (τ X0)
             grind)
          | exact resolve b6e953 b6e338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e953
        have b6e1023 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e614
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e614
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e614 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1025 : (k y x) = (τ (σ y)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e614
             grind)
          | exact superpose b6e614 b6e13
          | exact resolve b6e13 b6e614
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e614
        have b6e1043 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
        clear b6e1023
        have b6e1057 : x = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e1025
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1025
          | exact resolve b6e1025 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1025
        have b6e1058 : (σ y) = (σ (M.op y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e1043
             have r₂ := b6e21
             grind)
          | exact resolve b6e1043 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1043
        have b6e1060 : (σ y) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e1058
             have r₂ := b6e20
             grind)
          | exact resolve b6e1058 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1058
        have b6e1110 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op y x)
             have i₂ := b6e1060
             grind)
          | exact superpose b6e1060 b6e13
          | exact resolve b6e13 b6e1060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1121 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b6e95 X0 (M.op y x)
             have i₂ := b6e1060
             grind)
          | exact superpose b6e1060 b6e95
          | exact resolve b6e95 b6e1060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1134 : ∀ X0 : G, (k (τ X0) y) = (k (τ X0) (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b6e1121 X0
             have i₂ := b6e95 X0 y
             grind)
          | exact superpose b6e95 b6e1121
          | exact resolve b6e1121 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1121
        have b6e1141 : y = (M.op y x) := by
          first
          | (have i₁ := b6e1110
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1110
          | exact resolve b6e1110 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1110
        have b6e1253 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e1057
             grind)
          | exact superpose b6e1057 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e1057
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1057
        have b6e1255 : x = (M.op y x) ∨ y = (M.op x y) ∨ y = (k y x) := by grind
        clear b6e1253
        have b6e1257 : y = (M.op x y) ∨ y = (k y x) := by
          first
          | (have r₁ := b6e1255
             have r₂ := b6e21
             grind)
          | exact resolve b6e1255 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1255
        have b6e1258 : y = (k y x) := by
          first
          | (have r₁ := b6e1257
             have r₂ := b6e20
             grind)
          | exact resolve b6e1257 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1257
        have b6e1781 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e251 x x
             have i₂ := b6e75 (σ x)
             grind)
          | exact superpose b6e75 b6e251
          | (have j0 := b6e251 y X0
             grind)
          | exact resolve b6e251 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e251
        have b6e2022 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e169 (σ X0)
             have i₂ := b6e57 X0 y
             grind)
          | exact superpose b6e57 b6e169
          | (have j1 := b6e57 X0 y
             grind)
          | exact resolve b6e169 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e2033 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (k (τ (M.op (σ y) X0)) y) := by
          intro X0
          first
          | (have i₁ := b6e95 (M.op (σ y) X0) y
             have i₂ := b6e169 X0
             grind)
          | exact superpose b6e169 b6e95
          | exact resolve b6e95 b6e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e169
        have b6e2043 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have j0 := b6e2022 X0
             have j1 := b6e15 (σ X0) (σ y)
             grind)
          | (have r₁ := b6e2022 X0
             have r₂ := b6e15 (σ X0) (σ y)
             grind)
          | exact resolve b6e2022 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2022
        have b6e2051 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e2043 X0
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e2043
          | (have j0 := b6e2043 X0
             grind)
          | exact resolve b6e2043 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2043
        have b6e2115 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (σ X1) X2) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e232 X0 (τ X0) X2
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e232
          | exact resolve b6e232 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2161 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (M.op (σ X0) X3) = (M.op (σ X1) X3) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e40 (σ X0) (σ X1) X2
             have i₂ := b6e232 X0 X1 X3
             grind)
          | exact superpose b6e232 b6e40
          | (have j1 := b6e232 X0 X1 X3
             grind)
          | exact resolve b6e40 b6e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2181 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e45
             have i₂ := b6e232 y X0 (σ x)
             grind)
          | (have i₁ := b6e45
             have i₂ := b6e232 X0 y (σ x)
             grind)
          | exact superpose b6e232 b6e45
          | (have j1 := b6e232 y X0 x
             grind)
          | exact resolve b6e45 b6e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e2271 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e232 X0 X1 (σ X1)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e232
        have b6e2293 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e2181 X0
             have i₂ := b6e1258
             grind)
          | exact superpose b6e1258 b6e2181
          | (have j0 := b6e2181 X0
             grind)
          | exact resolve b6e2181 b6e1258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2181
        have b6e2311 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X2) = (M.op (σ X1) X2) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e2115 X0 X1 X2
             have i₂ := b6e28 X0 X1
             grind)
          | exact superpose b6e28 b6e2115
          | (have j0 := b6e2115 X0 X1 X2
             grind)
          | exact resolve b6e2115 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2115
        have b6e2347 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e2293 X0
             grind)
          | (have r₁ := b6e2293 X0
             have r₂ := b6e66
             grind)
          | exact resolve b6e2293 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2293
        have b6e2607 : (σ x) = (σ y) ∨ x = (k x x) := by
          first
          | (have i₁ := b6e753
             have i₂ := b6e1258
             grind)
          | exact superpose b6e1258 b6e753
          | exact resolve b6e753 b6e1258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e753 b6e1258
        have b6e2671 : x = (k x x) := by
          first
          | (have r₁ := b6e2607
             have r₂ := b6e66
             grind)
          | exact resolve b6e2607 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2607
        have b6e2824 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e237 x x
             have i₂ := b6e2671
             grind)
          | exact superpose b6e2671 b6e237
          | (have j0 := b6e237 x x
             grind)
          | exact resolve b6e237 b6e2671
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e237
        have b6e2825 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e2671
             grind)
          | exact superpose b6e2671 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e2671
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2671
        have b6e2826 : x = (M.op x x) := by grind
        clear b6e2825
        have b6e2827 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b6e2824
        have b6e2828 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b6e2827
        have b6e2832 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e2828
             have i₂ := b6e75 (σ x)
             grind)
          | exact superpose b6e75 b6e2828
          | exact resolve b6e2828 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2828
        have b6e2977 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (M.op x (M.op x X0)) ∨ (M.op x X0) = (k x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b6e79 x x X0
             have i₂ := b6e2826
             grind)
          | exact superpose b6e2826 b6e79
          | (have j0 := b6e79 x x X0
             grind)
          | (have r₁ := b6e79 x x x
             have r₂ := b6e2826
             grind)
          | exact resolve b6e79 b6e2826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e2985 : ∀ X0 : G, (M.op x X0) = (k x (M.op x X0)) ∨ (M.op x X0) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have j0 := b6e2977 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2977
        have b6e3144 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ y) X0) = (k (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e81 (σ y) (σ x) X0
             have i₂ := b6e2832
             grind)
          | exact superpose b6e2832 b6e81
          | (have j0 := b6e81 (σ y) (σ x) X0
             grind)
          | (have r₁ := b6e81 (σ y) (σ x) x
             have r₂ := b6e2832
             grind)
          | exact resolve b6e81 b6e2832
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3150 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e3144 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3144
        have b6e6349 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
          first
          | (have i₁ := b6e960 y
             have i₂ := b6e188
             grind)
          | exact superpose b6e188 b6e960
          | (have j0 := b6e960 y
             grind)
          | exact resolve b6e960 b6e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e188 b6e960
        have b6e6356 : (τ y) = (M.op (τ y) (τ y)) := by grind
        clear b6e6349
        have b6e15064 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e2311 X0 (τ X0) X2
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e2311
          | exact resolve b6e2311 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2311
        have b6e23702 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e203 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e203
        have b6e24191 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e3150 (σ X0)
             have i₂ := b6e230 X0
             grind)
          | exact superpose b6e230 b6e3150
          | (have j1 := b6e230 X0
             grind)
          | exact resolve b6e3150 b6e230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e230
        have b6e24254 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e24191 X0
             have j1 := b6e15 (σ X0) (σ x)
             grind)
          | (have r₁ := b6e24191 X0
             have r₂ := b6e15 (σ X0) (σ x)
             grind)
          | exact resolve b6e24191 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24191
        have b6e24315 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e24254 X0
             have i₂ := b6e18 X0 x
             grind)
          | exact superpose b6e18 b6e24254
          | (have j0 := b6e24254 X0
             grind)
          | exact resolve b6e24254 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24254
        have b6e26434 : ∀ X0 : G, (σ (k x X0)) = (σ (k y X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ (k x X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e2347 X0
             have i₂ := b6e1781 X0
             grind)
          | exact superpose b6e1781 b6e2347
          | (have j0 := b6e2347 X0
             have j1 := b6e1781 X0
             grind)
          | exact resolve b6e2347 b6e1781
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1781 b6e2347
        have b6e26667 : ∀ X0 : G, (σ (k x X0)) = (σ (k y X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ (k x X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e26434 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26434
        have b6e26724 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have j0 := b6e26667 X0
             have j1 := b6e23702 X0
             grind)
          | (have r₁ := b6e26667 X0
             have r₂ := b6e23702 X0
             grind)
          | exact resolve b6e26667 b6e23702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23702 b6e26667
        have b6e32242 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k (τ X0) y)) ∨ (σ (k (τ X0) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e2051 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e2051
          | exact resolve b6e2051 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32393 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 y)) X1) ∨ (σ X0) = (σ (k X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 (σ X0) (σ y) X1
             have i₂ := b6e2051 X0
             grind)
          | exact superpose b6e2051 b6e40
          | (have j1 := b6e2051 X0
             grind)
          | exact resolve b6e40 b6e2051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2051
        have b6e32472 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ (k (τ X0) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32242 X0
             have i₂ := b6e27 X0 y
             grind)
          | exact superpose b6e27 b6e32242
          | (have j0 := b6e32242 X0
             grind)
          | exact resolve b6e32242 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32242
        have b6e32505 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32472 X0
             have i₂ := b6e27 X0 y
             grind)
          | exact superpose b6e27 b6e32472
          | (have j0 := b6e32472 X0
             grind)
          | exact resolve b6e32472 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32472
        have b6e37234 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (M.op (σ (τ X0)) X3) = (M.op (σ (τ X1)) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e2161 (τ X0) (τ X1) X2 X3
             have i₂ := b6e338 X1 X0
             grind)
          | exact superpose b6e338 b6e2161
          | (have j0 := b6e2161 (τ X0) (τ X1) X2 X3
             grind)
          | exact resolve b6e2161 b6e338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2161
        have b6e38139 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X2) = (M.op (k X0 X1) X2) ∨ (M.op (σ (τ X0)) X3) = (M.op (σ (τ X1)) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e37234 X0 X1 X2 X3
             have i₂ := b6e14 (k X0 X1)
             grind)
          | exact superpose b6e14 b6e37234
          | (have j0 := b6e37234 X0 X1 X2 X3
             grind)
          | exact resolve b6e37234 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37234
        have b6e38207 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (M.op (σ (τ X0)) X3) = (M.op (σ (τ X1)) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e38139 X0 X1 X2 X3
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e38139
          | (have j0 := b6e38139 X0 X1 X2 X3
             grind)
          | exact resolve b6e38139 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38139
        have b6e38253 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X3) = (M.op X1 X3) ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e38207 X0 X1 X2 X3
             have i₂ := b6e14 X1
             grind)
          | exact superpose b6e14 b6e38207
          | (have j0 := b6e38207 X0 X1 X2 X3
             grind)
          | exact resolve b6e38207 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38207
        have b6e38289 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op X1 X3) ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e38253 X0 X1 X2 X3
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e38253
          | (have j0 := b6e38253 X0 X1 X2 X3
             grind)
          | exact resolve b6e38253 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38253
        have b6e38314 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X3) = (M.op X1 X3) ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e38289 X0 X0 X2 X3
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e38289
          | (have j0 := b6e38289 X0 X1 X2 X3
             grind)
          | exact resolve b6e38289 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38289
        have b6e38331 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (M.op X0 X3) = (M.op X1 X3) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e38314 X0 X1 X2 X3
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e38314
          | (have j0 := b6e38314 X0 X1 X2 X3
             grind)
          | exact resolve b6e38314 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38314
        have b6e41342 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e2271 (τ X0) (τ X1)
             have i₂ := b6e338 X1 X0
             grind)
          | exact superpose b6e338 b6e2271
          | (have j0 := b6e2271 (τ X0) (τ X1)
             grind)
          | exact resolve b6e2271 b6e338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41343 : ∀ X0 : G, (M.op (σ (M.op y x)) (σ (M.op y x))) ≠ (σ (k (τ X0) y)) ∨ (M.op (σ (M.op y x)) (σ (M.op y x))) = (M.op (σ (τ X0)) (σ (M.op y x))) ∨ (σ (M.op y x)) = (M.op (σ (τ X0)) (σ (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b6e2271 (τ X0) (M.op y x)
             have i₂ := b6e1134 X0
             grind)
          | exact superpose b6e1134 b6e2271
          | (have j0 := b6e2271 (τ X0) (M.op y x)
             grind)
          | exact resolve b6e2271 b6e1134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1134 b6e2271
        have b6e41593 : ∀ X0 : G, (k X0 (σ y)) ≠ (M.op (σ (M.op y x)) (σ (M.op y x))) ∨ (M.op (σ (M.op y x)) (σ (M.op y x))) = (M.op (σ (τ X0)) (σ (M.op y x))) ∨ (σ (M.op y x)) = (M.op (σ (τ X0)) (σ (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b6e41343 X0
             have i₂ := b6e27 X0 y
             grind)
          | exact superpose b6e27 b6e41343
          | (have j0 := b6e41343 X0
             grind)
          | exact resolve b6e41343 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41343
        have b6e41594 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e41342 X0 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e41342
          | (have j0 := b6e41342 X0 X1
             grind)
          | exact resolve b6e41342 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41342
        have b6e41673 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (k X0 (σ y)) ∨ (M.op (σ (M.op y x)) (σ (M.op y x))) = (M.op (σ (τ X0)) (σ (M.op y x))) ∨ (σ (M.op y x)) = (M.op (σ (τ X0)) (σ (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b6e41593 X0
             have i₂ := b6e1060
             grind)
          | exact superpose b6e1060 b6e41593
          | (have j0 := b6e41593 X0
             grind)
          | exact resolve b6e41593 b6e1060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41593
        have b6e41674 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e41594 X0 X1
             have i₂ := b6e14 (k X0 X1)
             grind)
          | exact superpose b6e14 b6e41594
          | (have j0 := b6e41594 X0 X1
             grind)
          | exact resolve b6e41594 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41594
        have b6e41727 : ∀ X0 : G, (σ y) ≠ (k X0 (σ y)) ∨ (M.op (σ (M.op y x)) (σ (M.op y x))) = (M.op (σ (τ X0)) (σ (M.op y x))) ∨ (σ (M.op y x)) = (M.op (σ (τ X0)) (σ (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b6e41673 X0
             have i₂ := b6e130
             grind)
          | exact superpose b6e130 b6e41673
          | (have j0 := b6e41673 X0
             grind)
          | exact resolve b6e41673 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41673
        have b6e41728 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e41674 X0 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e41674
          | (have j0 := b6e41674 X0 X1
             grind)
          | exact resolve b6e41674 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41674
        have b6e41772 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ (τ X0)) (σ y)) ∨ (σ y) ≠ (k X0 (σ y)) ∨ (σ (M.op y x)) = (M.op (σ (τ X0)) (σ (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b6e41727 X0
             have i₂ := b6e1060
             grind)
          | exact superpose b6e1060 b6e41727
          | (have j0 := b6e41727 X0
             grind)
          | exact resolve b6e41727 b6e1060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41727
        have b6e41773 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e41728 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e41728
          | (have j0 := b6e41728 X0 X1
             grind)
          | exact resolve b6e41728 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41728
        have b6e41810 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k X0 (σ y)) ∨ (σ (M.op y x)) = (M.op (σ (τ X0)) (σ (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b6e41772 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e41772
          | (have j0 := b6e41772 X0
             grind)
          | exact resolve b6e41772 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41772
        have b6e41811 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e41773 X0 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e41773
          | (have j0 := b6e41773 X0 X1
             grind)
          | exact resolve b6e41773 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41773
        have b6e41844 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) ≠ (k X0 (σ y)) ∨ (σ (M.op y x)) = (M.op (σ (τ X0)) (σ (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b6e41810 X0
             have i₂ := b6e130
             grind)
          | exact superpose b6e130 b6e41810
          | (have j0 := b6e41810 X0
             grind)
          | exact resolve b6e41810 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41810
        have b6e41845 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e41811 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e41811
          | (have j0 := b6e41811 X0 X1
             grind)
          | exact resolve b6e41811 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41811
        have b6e41851 : ∀ X0 : G, (σ y) = (M.op (σ (τ X0)) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) ≠ (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e41844 X0
             have i₂ := b6e1060
             grind)
          | exact superpose b6e1060 b6e41844
          | (have j0 := b6e41844 X0
             grind)
          | exact resolve b6e41844 b6e1060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1060 b6e41844
        have b6e41856 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) ≠ (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e41851 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e41851
          | (have j0 := b6e41851 X0
             grind)
          | exact resolve b6e41851 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41851
        have b6e41857 : ∀ X0 : G, (σ y) ≠ (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e41856 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41856
        have b6e46199 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (k (τ X0) x)) ∨ (σ (k (τ X0) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e24315 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e24315
          | exact resolve b6e24315 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24315
        have b6e46524 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ (k (τ X0) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e46199 X0
             have i₂ := b6e27 X0 x
             grind)
          | exact superpose b6e27 b6e46199
          | (have j0 := b6e46199 X0
             grind)
          | exact resolve b6e46199 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46199
        have b6e46599 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e46524 X0
             have i₂ := b6e27 X0 x
             grind)
          | exact superpose b6e27 b6e46524
          | (have j0 := b6e46524 X0
             grind)
          | exact resolve b6e46524 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46524
        have b6e417428 : ∀ X0 : G, (τ y) = (M.op X0 (τ y)) ∨ (M.op X0 (τ y)) = (k X0 (τ y)) ∨ (τ y) = (M.op X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b6e6356
             have i₂ := b6e15064 X0 (τ y) (τ y)
             grind)
          | (have i₁ := b6e6356
             have i₂ := b6e15064 (τ y) x (τ y)
             grind)
          | exact superpose b6e15064 b6e6356
          | (have j1 := b6e15064 X0 (τ y) x
             grind)
          | exact resolve b6e6356 b6e15064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e417442 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) y) ∨ (k X0 y) = (M.op X0 y) ∨ y = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b6e336 x
             have i₂ := b6e15064 y X1 x
             grind)
          | (have i₁ := b6e336 x
             have i₂ := b6e15064 X0 y x
             grind)
          | exact superpose b6e15064 b6e336
          | (have j1 := b6e15064 X0 y x
             grind)
          | exact resolve b6e336 b6e15064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e417526 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e15064 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15064
        have b6e417547 : ∀ X0 : G, (M.op X0 (τ y)) = (k X0 (τ y)) ∨ (τ y) = (M.op X0 (τ y)) := by
          intro X0
          first
          | (have j0 := b6e417428 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e417428
        have b6e417615 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) y) ∨ (k X0 y) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have j0 := b6e417442 X0 X1
             have j1 := b6e81 X0 y X1
             grind)
          | (have r₁ := b6e417442 X0 X1
             have r₂ := b6e81 X0 y x
             grind)
          | exact resolve b6e417442 b6e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81 b6e417442
        have b6e418290 : ∀ X0 : G, (k (σ X0) y) = (σ (M.op X0 (τ y))) ∨ (τ y) = (M.op X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b6e28 y X0
             have i₂ := b6e417547 X0
             grind)
          | exact superpose b6e417547 b6e28
          | (have j1 := b6e417547 X0
             grind)
          | exact resolve b6e28 b6e417547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e419098 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) y) ∨ (k (M.op X0 X2) y) = (M.op (M.op X0 X2) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e417615 (M.op X0 X2) x
             have i₂ := b6e40 X0 X2 x
             grind)
          | exact superpose b6e40 b6e417615
          | (have j0 := b6e417615 X0 X1
             grind)
          | exact resolve b6e417615 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e419121 : (σ y) = (k (σ y) y) ∨ (M.op (σ x) y) = (k (σ x) y) := by
          first
          | (have i₁ := b6e417615 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e417615
          | (have j0 := b6e417615 (σ x) x
             grind)
          | exact resolve b6e417615 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e419122 : (σ x) = (k (σ x) y) ∨ (M.op (σ y) y) = (k (σ y) y) := by
          first
          | (have i₁ := b6e417615 (σ y) (σ x)
             have i₂ := b6e2832
             grind)
          | exact superpose b6e2832 b6e417615
          | (have j0 := b6e417615 (σ y) x
             grind)
          | exact resolve b6e417615 b6e2832
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e419124 : (M.op (σ y) y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b6e417615 (σ y) (σ y)
             have i₂ := b6e130
             grind)
          | exact superpose b6e130 b6e417615
          | (have j0 := b6e417615 (σ y) x
             grind)
          | exact resolve b6e417615 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130 b6e417615
        have b6e419203 : (M.op (σ y) y) = (k (σ x) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b6e419121
             have i₂ := b6e75 y
             grind)
          | exact superpose b6e75 b6e419121
          | exact resolve b6e419121 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e419121
        have b6e419206 : ∀ X0 X1 X2 : G, (M.op X0 y) = (k (M.op X0 X2) y) ∨ (M.op X0 X1) = (k (M.op X0 X1) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e419098 X0 X1 X2
             have i₂ := b6e40 X0 X2 y
             grind)
          | exact superpose b6e40 b6e419098
          | (have j0 := b6e419098 X0 X1 X2
             grind)
          | exact resolve b6e419098 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e419098
        have b6e420910 : (τ (σ x)) = (k x (τ y)) ∨ (M.op (σ y) y) = (k (σ y) y) := by
          first
          | (have i₁ := b6e102 x y
             have i₂ := b6e419122
             grind)
          | exact superpose b6e419122 b6e102
          | exact resolve b6e102 b6e419122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e419122
        have b6e420945 : (M.op (σ y) y) = (k (σ y) y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e420910
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e420910
          | exact resolve b6e420910 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e420910
        have b6e426193 : (k y (τ y)) = (τ (M.op (σ y) y)) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b6e102 y y
             have i₂ := b6e419124
             grind)
          | exact superpose b6e419124 b6e102
          | exact resolve b6e102 b6e419124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e419124
        have b6e430000 : (k x (τ y)) = (τ (M.op (σ y) y)) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b6e102 x y
             have i₂ := b6e419203
             grind)
          | exact superpose b6e419203 b6e102
          | exact resolve b6e102 b6e419203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e419203
        have b6e440921 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e417526 X0 x
             have i₂ := b6e2826
             grind)
          | exact superpose b6e2826 b6e417526
          | (have j0 := b6e417526 X0 x
             grind)
          | (have r₁ := b6e417526 X0 x
             have r₂ := b6e2826
             grind)
          | exact resolve b6e417526 b6e2826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e440922 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e417526 X0 y
             have i₂ := b6e285
             grind)
          | exact superpose b6e285 b6e417526
          | (have j0 := b6e417526 X0 y
             grind)
          | (have r₁ := b6e417526 X0 y
             have r₂ := b6e285
             grind)
          | exact resolve b6e417526 b6e285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e417526
        have b6e440923 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b6e440922 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e440922
        have b6e440924 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b6e440921 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e440921
        have b6e443120 : ∀ X0 : G, (k X0 (τ y)) = (τ (M.op (σ X0) y)) ∨ y = (M.op (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b6e102 X0 y
             have i₂ := b6e440923 (σ X0)
             grind)
          | exact superpose b6e440923 b6e102
          | (have j1 := b6e440923 (σ X0)
             grind)
          | exact resolve b6e102 b6e440923
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e444167 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) x)) ∨ x = (M.op (σ X0) x) := by
          intro X0
          first
          | (have i₁ := b6e102 X0 x
             have i₂ := b6e440924 (σ X0)
             grind)
          | exact superpose b6e440924 b6e102
          | (have j1 := b6e440924 (σ X0)
             grind)
          | exact resolve b6e102 b6e440924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e440924
        have b6e445471 : (k x (τ y)) = (τ (M.op (σ y) y)) ∨ y = (M.op (σ y) y) := by
          first
          | (have i₁ := b6e443120 x
             have i₂ := b6e75 y
             grind)
          | exact superpose b6e75 b6e443120
          | (have j0 := b6e443120 y
             grind)
          | exact resolve b6e443120 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e447273 : (k y (τ y)) = (k x (τ y)) ∨ y = (M.op (σ y) y) ∨ y = (M.op (σ y) y) := by
          first
          | (have i₁ := b6e443120 y
             have i₂ := b6e445471
             grind)
          | exact superpose b6e445471 b6e443120
          | (have j0 := b6e443120 y
             grind)
          | exact resolve b6e443120 b6e445471
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e445471
        have b6e447313 : (k y (τ y)) = (k x (τ y)) ∨ y = (M.op (σ y) y) := by grind
        clear b6e447273
        have b6e449401 : (k x (τ x)) = (τ (M.op (σ y) x)) ∨ x = (M.op (σ y) x) := by
          first
          | (have i₁ := b6e444167 x
             have i₂ := b6e75 x
             grind)
          | exact superpose b6e75 b6e444167
          | (have j0 := b6e444167 y
             grind)
          | exact resolve b6e444167 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e467852 : (k y (τ y)) = (k x (τ y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b6e426193
             have i₂ := b6e430000
             grind)
          | exact superpose b6e430000 b6e426193
          | exact resolve b6e426193 b6e430000
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e426193 b6e430000
        have b6e467894 : (σ y) = (k (σ y) y) ∨ (k y (τ y)) = (k x (τ y)) := by grind
        clear b6e467852
        have b6e468773 : (τ (σ y)) = (k y (τ y)) ∨ (k y (τ y)) = (k x (τ y)) := by
          first
          | (have i₁ := b6e102 y y
             have i₂ := b6e467894
             grind)
          | exact superpose b6e467894 b6e102
          | exact resolve b6e102 b6e467894
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e467894
        have b6e468795 : (k y (τ y)) = (k x (τ y)) ∨ y = (k y (τ y)) := by
          first
          | (have i₁ := b6e468773
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e468773
          | exact resolve b6e468773 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e468773
        have b6e499094 : ∀ X0 : G, (M.op (σ y) y) = (k (M.op (σ y) X0) y) ∨ (σ x) = (k (σ x) y) := by
          intro X0
          first
          | (have i₁ := b6e419206 (σ y) (σ x) x
             have i₂ := b6e2832
             grind)
          | exact superpose b6e2832 b6e419206
          | (have j0 := b6e419206 (σ y) x X0
             grind)
          | exact resolve b6e419206 b6e2832
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e499204 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 y) ∨ (M.op X0 X1) = (k (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have j0 := b6e419206 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e419206
        have b6e500234 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) y) := by
          intro X0
          first
          | (have j0 := b6e499204 X0 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e499204
        have b6e519957 : (M.op (σ y) y) = (k (σ x) y) ∨ (σ x) = (k (σ x) y) := by
          first
          | (have i₁ := b6e499094 (σ x)
             have i₂ := b6e2832
             grind)
          | exact superpose b6e2832 b6e499094
          | exact resolve b6e499094 b6e2832
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2832 b6e499094
        have b6e520661 : (k x (τ y)) = (τ (M.op (σ y) y)) ∨ (σ x) = (k (σ x) y) := by
          first
          | (have i₁ := b6e102 x y
             have i₂ := b6e519957
             grind)
          | exact superpose b6e519957 b6e102
          | exact resolve b6e102 b6e519957
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e519957
        have b6e521349 : (k y (τ y)) = (k x (τ y)) ∨ (σ x) = (k (σ x) y) ∨ y = (M.op (σ y) y) := by
          first
          | (have i₁ := b6e520661
             have i₂ := b6e443120 y
             grind)
          | exact superpose b6e443120 b6e520661
          | (have j1 := b6e443120 y
             grind)
          | exact resolve b6e520661 b6e443120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e443120 b6e520661
        have b6e521393 : (σ x) = (k (σ x) y) ∨ (k y (τ y)) = (k x (τ y)) := by
          first
          | (have j1 := b6e134 y
             grind)
          | (have r₁ := b6e521349
             have r₂ := b6e134 y
             grind)
          | exact resolve b6e521349 b6e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134 b6e521349
        have b6e521984 : (τ (σ x)) = (k x (τ y)) ∨ (k y (τ y)) = (k x (τ y)) := by
          first
          | (have i₁ := b6e102 x y
             have i₂ := b6e521393
             grind)
          | exact superpose b6e521393 b6e102
          | exact resolve b6e102 b6e521393
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e521393
        have b6e522039 : (k y (τ y)) = (k x (τ y)) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e521984
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e521984
          | exact resolve b6e521984 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e521984
        have b6e527091 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e41845 X0 (M.op X1 X1)
             have i₂ := b6e12 X1 X1 X1
             grind)
          | exact superpose b6e12 b6e41845
          | (have j0 := b6e41845 X1 (M.op X0 X0)
             grind)
          | exact resolve b6e41845 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41845
        have b6e527164 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e527091 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e527091
        have b6e527191 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 (M.op X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e527164 X0 X1
             have i₂ := b6e39 X0 X1
             grind)
          | exact superpose b6e39 b6e527164
          | (have j0 := b6e527164 X0 X1
             grind)
          | exact resolve b6e527164 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39 b6e527164
        have b6e528134 : ∀ X0 : G, x ≠ (k X0 x) ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e527191 x x
             have i₂ := b6e2826
             grind)
          | exact superpose b6e2826 b6e527191
          | exact resolve b6e527191 b6e2826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2826
        have b6e528135 : ∀ X0 : G, y ≠ (k X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e527191 y x
             have i₂ := b6e285
             grind)
          | exact superpose b6e285 b6e527191
          | exact resolve b6e527191 b6e285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e285 b6e527191
        have b6e531628 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have j0 := b6e38331 X0 X1 X2 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38331
        have b6e554479 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b6e3150 (σ X0)
             have i₂ := b6e26724 X0
             grind)
          | exact superpose b6e26724 b6e3150
          | (have j1 := b6e26724 X0
             grind)
          | exact resolve b6e3150 b6e26724
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3150 b6e26724
        have b6e554496 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have j0 := b6e554479 X0
             have j1 := b6e15 (σ X0) (σ x)
             grind)
          | (have r₁ := b6e554479 X0
             have r₂ := b6e15 (σ X0) (σ x)
             grind)
          | exact resolve b6e554479 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554479
        have b6e554509 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) ∨ (σ (k x X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b6e554496 X0
             have i₂ := b6e18 X0 x
             grind)
          | exact superpose b6e18 b6e554496
          | (have j0 := b6e554496 X0
             grind)
          | exact resolve b6e554496 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554496
        have b6e554580 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (σ (k y (τ X0))) = (σ (k x (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e27 X0 x
             have i₂ := b6e554509 (τ X0)
             grind)
          | exact superpose b6e554509 b6e27
          | (have j1 := b6e554509 (τ X0)
             grind)
          | exact resolve b6e27 b6e554509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e554667 : ∀ X0 : G, (k x X0) = (τ (σ (k y X0))) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e13 (k x X0)
             have i₂ := b6e554509 X0
             grind)
          | exact superpose b6e554509 b6e13
          | (have j1 := b6e554509 X0
             grind)
          | exact resolve b6e13 b6e554509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554509
        have b6e554710 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) ∨ (k x X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e554667 X0
             have i₂ := b6e13 (k y X0)
             grind)
          | exact superpose b6e13 b6e554667
          | (have j0 := b6e554667 X0
             grind)
          | exact resolve b6e554667 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554667
        have b6e554743 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ (k y (τ X0))) = (σ (k x (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e554580 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e554580
          | (have j0 := b6e554580 X0
             grind)
          | exact resolve b6e554580 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554580
        have b6e554772 : ∀ X0 : G, (k (σ x) X0) = (σ (k y (τ X0))) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e554743 X0
             have i₂ := b6e28 X0 x
             grind)
          | exact superpose b6e28 b6e554743
          | (have j0 := b6e554743 X0
             grind)
          | exact resolve b6e554743 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554743
        have b6e554790 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e554772 X0
             have i₂ := b6e28 X0 y
             grind)
          | exact superpose b6e28 b6e554772
          | (have j0 := b6e554772 X0
             grind)
          | exact resolve b6e554772 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554772
        have b6e554965 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (k x X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 x)
             have i₂ := b6e554710 X0
             grind)
          | exact superpose b6e554710 b6e13
          | (have j1 := b6e554710 X0
             grind)
          | exact resolve b6e13 b6e554710
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554710
        have b6e555048 : ∀ X0 : G, (k X0 x) = X0 ∨ (k x X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e554965 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e554965
          | (have j0 := b6e554965 X0
             grind)
          | exact resolve b6e554965 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554965
        have b6e555243 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ x)) ∨ (k y (σ X0)) = (k x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e102 X0 x
             have i₂ := b6e555048 (σ X0)
             grind)
          | exact superpose b6e555048 b6e102
          | (have j1 := b6e555048 (σ X0)
             grind)
          | exact resolve b6e102 b6e555048
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e555048
        have b6e555763 : ∀ X0 : G, (k X0 (τ x)) = X0 ∨ (k y (σ X0)) = (k x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e555243 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e555243
          | (have j0 := b6e555243 X0
             grind)
          | exact resolve b6e555243 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e555243
        have b6e557178 : ∀ X0 : G, (k (τ x) X0) = (τ (k y (σ X0))) ∨ (k X0 (τ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e95 x X0
             have i₂ := b6e555763 X0
             grind)
          | exact superpose b6e555763 b6e95
          | (have j1 := b6e555763 X0
             grind)
          | exact resolve b6e95 b6e555763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e557207 : ∀ X0 : G, (k (τ y) X0) = (k (τ x) X0) ∨ (k X0 (τ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e557178 X0
             have i₂ := b6e95 y X0
             grind)
          | exact superpose b6e95 b6e557178
          | (have j0 := b6e557178 X0
             grind)
          | exact resolve b6e557178 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95 b6e557178
        have b6e557680 : ∀ X0 : G, (σ X0) = (k (σ X0) x) ∨ (k (τ y) X0) = (k (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e28 x X0
             have i₂ := b6e557207 X0
             grind)
          | exact superpose b6e557207 b6e28
          | (have j1 := b6e557207 X0
             grind)
          | exact resolve b6e28 b6e557207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e557207
        have b6e573692 : ∀ X0 X1 : G, (τ y) ≠ (τ y) ∨ (M.op X0 X1) = (M.op (k X0 (τ y)) X1) ∨ (τ y) = (M.op X0 (τ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e531628 X0 (τ y) X1
             have i₂ := b6e6356
             grind)
          | exact superpose b6e6356 b6e531628
          | (have j0 := b6e531628 X0 (τ y) X1
             grind)
          | (have r₁ := b6e531628 X0 (τ y) x
             have r₂ := b6e6356
             grind)
          | exact resolve b6e531628 b6e6356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6356 b6e531628
        have b6e573697 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 (τ y)) X1) ∨ (τ y) = (M.op X0 (τ y)) := by
          intro X0 X1
          first
          | (have j0 := b6e573692 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e573692
        have b6e573718 : ∀ X0 : G, (M.op x X0) = (M.op (k y (τ y)) X0) ∨ (τ y) = (M.op x (τ y)) ∨ x = (k x (τ y)) := by
          intro X0
          first
          | (have i₁ := b6e573697 x X0
             have i₂ := b6e522039
             grind)
          | exact superpose b6e522039 b6e573697
          | (have j0 := b6e573697 x x
             grind)
          | exact resolve b6e573697 b6e522039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e522039 b6e573697
        have b6e573813 : ∀ X0 : G, (M.op x X0) = (M.op (k y (τ y)) X0) ∨ x = (k x (τ y)) := by
          intro X0
          first
          | (have j0 := b6e573718 X0
             have j1 := b6e15 x (τ y)
             grind)
          | (have r₁ := b6e573718 X0
             have r₂ := b6e15 x (τ y)
             grind)
          | exact resolve b6e573718 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e573718
        have b6e573927 : (σ (M.op x (τ y))) = (k (σ (k y (τ y))) y) ∨ (τ y) = (M.op x (τ y)) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e418290 (k y (τ y))
             have i₂ := b6e573813 (τ y)
             grind)
          | exact superpose b6e573813 b6e418290
          | (have j0 := b6e418290 x
             grind)
          | exact resolve b6e418290 b6e573813
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e573813
        have b6e573951 : (σ (M.op x (τ y))) = (k (σ (k y (τ y))) y) ∨ x = (k x (τ y)) := by
          first
          | (have j1 := b6e15 x (τ y)
             grind)
          | (have r₁ := b6e573927
             have r₂ := b6e15 x (τ y)
             grind)
          | exact resolve b6e573927 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e573927
        have b6e573965 : (k (k (σ y) y) y) = (σ (M.op x (τ y))) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e573951
             have i₂ := b6e28 y y
             grind)
          | exact superpose b6e28 b6e573951
          | exact resolve b6e573951 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e573951
        have b6e574347 : (k (M.op (σ y) y) y) = (σ (M.op x (τ y))) ∨ x = (k x (τ y)) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e573965
             have i₂ := b6e420945
             grind)
          | exact superpose b6e420945 b6e573965
          | exact resolve b6e573965 b6e420945
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e420945 b6e573965
        have b6e574370 : (k (M.op (σ y) y) y) = (σ (M.op x (τ y))) ∨ x = (k x (τ y)) := by grind
        clear b6e574347
        have b6e574379 : (M.op (σ y) y) = (σ (M.op x (τ y))) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e574370
             have i₂ := b6e500234 (σ y)
             grind)
          | exact superpose b6e500234 b6e574370
          | exact resolve b6e574370 b6e500234
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e500234 b6e574370
        have b6e574403 : (M.op (σ y) y) = (k (σ x) y) ∨ (τ y) = (M.op x (τ y)) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e418290 x
             have i₂ := b6e574379
             grind)
          | exact superpose b6e574379 b6e418290
          | (have j0 := b6e418290 x
             grind)
          | exact resolve b6e418290 b6e574379
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e418290
        have b6e574404 : (τ (M.op (σ y) y)) = (M.op x (τ y)) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e13 (M.op x (τ y))
             have i₂ := b6e574379
             grind)
          | exact superpose b6e574379 b6e13
          | exact resolve b6e13 b6e574379
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574379
        have b6e574423 : (M.op (σ y) y) = (k (σ x) y) ∨ x = (k x (τ y)) := by
          first
          | (have j1 := b6e15 x (τ y)
             grind)
          | (have r₁ := b6e574403
             have r₂ := b6e15 x (τ y)
             grind)
          | exact resolve b6e574403 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574403
        have b6e574476 : (k x (τ y)) = (τ (M.op (σ y) y)) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e102 x y
             have i₂ := b6e574423
             grind)
          | exact superpose b6e574423 b6e102
          | exact resolve b6e102 b6e574423
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102 b6e574423
        have b6e574587 : (M.op x (τ y)) = (k (M.op x (τ y)) y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e2033 y
             have i₂ := b6e574404
             grind)
          | exact superpose b6e574404 b6e2033
          | exact resolve b6e2033 b6e574404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2033
        have b6e574630 : (k x (τ y)) = (M.op x (τ y)) ∨ x = (k x (τ y)) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e574404
             have i₂ := b6e574476
             grind)
          | exact superpose b6e574476 b6e574404
          | exact resolve b6e574404 b6e574476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574404 b6e574476
        have b6e574656 : (k x (τ y)) = (M.op x (τ y)) ∨ x = (k x (τ y)) := by grind
        clear b6e574630
        have b6e574738 : x ≠ (M.op x (τ y)) ∨ x = (k x (τ y)) := by grind
        clear b6e574656
        have b6e574783 : (M.op x (τ y)) = (M.op (M.op x (τ y)) y) ∨ y = (M.op (M.op x (τ y)) y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e440923 (M.op x (τ y))
             have i₂ := b6e574587
             grind)
          | exact superpose b6e574587 b6e440923
          | (have j0 := b6e440923 (M.op x (τ y))
             grind)
          | exact resolve b6e440923 b6e574587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e440923 b6e574587
        have b6e574790 : (M.op x y) = (M.op x (τ y)) ∨ y = (M.op (M.op x (τ y)) y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e574783
             have i₂ := b6e40 x (τ y) y
             grind)
          | exact superpose b6e40 b6e574783
          | exact resolve b6e574783 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574783
        have b6e574796 : x = (M.op x (τ y)) ∨ y = (M.op (M.op x (τ y)) y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e574790
             have i₂ := b6e64
             grind)
          | exact superpose b6e64 b6e574790
          | exact resolve b6e574790 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e574790
        have b6e574802 : y = (M.op (M.op x (τ y)) y) ∨ x = (k x (τ y)) := by
          first
          | (have r₁ := b6e574796
             have r₂ := b6e574738
             grind)
          | exact resolve b6e574796 b6e574738
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574738 b6e574796
        have b6e574806 : y = (M.op x y) ∨ x = (k x (τ y)) := by
          first
          | (have i₁ := b6e574802
             have i₂ := b6e40 x (τ y) y
             grind)
          | exact superpose b6e40 b6e574802
          | exact resolve b6e574802 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574802
        have b6e574808 : x = (k x (τ y)) := by
          first
          | (have r₁ := b6e574806
             have r₂ := b6e20
             grind)
          | exact resolve b6e574806 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574806
        have b6e574842 : x = (k y (τ y)) ∨ y = (M.op (σ y) y) := by
          first
          | (have i₁ := b6e447313
             have i₂ := b6e574808
             grind)
          | exact superpose b6e574808 b6e447313
          | exact resolve b6e447313 b6e574808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e447313
        have b6e574845 : x = (k y (τ y)) ∨ y = (k y (τ y)) := by
          first
          | (have i₁ := b6e468795
             have i₂ := b6e574808
             grind)
          | exact superpose b6e574808 b6e468795
          | exact resolve b6e468795 b6e574808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e468795
        have b6e574895 : (σ x) = (k (σ x) y) := by
          first
          | (have i₁ := b6e28 y x
             have i₂ := b6e574808
             grind)
          | exact superpose b6e574808 b6e28
          | exact resolve b6e28 b6e574808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574808
        have b6e575029 : (σ x) = (k (σ y) y) ∨ y = (k y (σ x)) := by
          first
          | (have i₁ := b6e554790 y
             have i₂ := b6e574895
             grind)
          | exact superpose b6e574895 b6e554790
          | (have j0 := b6e554790 y
             grind)
          | exact resolve b6e554790 b6e574895
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554790 b6e574895
        have b6e575420 : x = (M.op y (τ y)) ∨ (τ y) = (M.op y (τ y)) ∨ y = (k y (τ y)) := by
          first
          | (have i₁ := b6e417547 y
             have i₂ := b6e574845
             grind)
          | exact superpose b6e574845 b6e417547
          | (have j0 := b6e417547 y
             grind)
          | exact resolve b6e417547 b6e574845
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e417547 b6e574845
        have b6e575477 : y = (k y (τ y)) ∨ x = (M.op y (τ y)) := by
          first
          | (have j1 := b6e15 y (τ y)
             grind)
          | (have r₁ := b6e575420
             have r₂ := b6e15 y (τ y)
             grind)
          | exact resolve b6e575420 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e575420
        have b6e575677 : x = y ∨ y = (M.op (σ y) y) ∨ x = (M.op y (τ y)) := by
          first
          | (have i₁ := b6e574842
             have i₂ := b6e575477
             grind)
          | exact superpose b6e575477 b6e574842
          | exact resolve b6e574842 b6e575477
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e574842 b6e575477
        have b6e575714 : y = (M.op (σ y) y) ∨ x = (M.op y (τ y)) := by
          first
          | (have r₁ := b6e575677
             have r₂ := b6e67
             grind)
          | exact resolve b6e575677 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e575677
        have b6e575924 : y ≠ y ∨ (σ y) = (M.op y (σ y)) ∨ (σ y) = (k y (σ y)) ∨ x = (M.op y (τ y)) := by
          first
          | (have i₁ := b6e16 y (σ y)
             have i₂ := b6e575714
             grind)
          | exact superpose b6e575714 b6e16
          | (have j0 := b6e16 y (σ y)
             grind)
          | (have r₁ := b6e16 y (σ y)
             have r₂ := b6e575714
             grind)
          | exact resolve b6e16 b6e575714
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e575714
        have b6e575966 : (σ y) = (M.op y (σ y)) ∨ (σ y) = (k y (σ y)) ∨ x = (M.op y (τ y)) := by grind
        clear b6e575924
        have b6e575978 : x = (M.op y (τ y)) ∨ (σ y) = (M.op y (σ y)) := by
          first
          | (have j1 := b6e41857 y
             grind)
          | (have r₁ := b6e575966
             have r₂ := b6e41857 y
             grind)
          | exact resolve b6e575966 b6e41857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41857 b6e575966
        have b6e580133 : x = (k y x) ∨ x = (M.op y x) ∨ (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b6e337 (τ y)
             have i₂ := b6e575978
             grind)
          | exact superpose b6e575978 b6e337
          | exact resolve b6e337 b6e575978
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e337 b6e575978
        have b6e580207 : x = (M.op y x) ∨ (σ y) = (M.op y (σ y)) := by
          first
          | (have j1 := b6e528134 y
             grind)
          | (have r₁ := b6e580133
             have r₂ := b6e528134 y
             grind)
          | exact resolve b6e580133 b6e528134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e528134 b6e580133
        have b6e580214 : (σ y) = (M.op y (σ y)) := by
          first
          | (have r₁ := b6e580207
             have r₂ := b6e21
             grind)
          | exact resolve b6e580207 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580207
        have b6e580230 : (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b6e336 (σ y)
             have i₂ := b6e580214
             grind)
          | exact superpose b6e580214 b6e336
          | exact resolve b6e336 b6e580214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e336
        have b6e580249 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e40 y (σ y) X0
             have i₂ := b6e580214
             grind)
          | exact superpose b6e580214 b6e40
          | exact resolve b6e40 b6e580214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e580499 : (σ x) = (σ y) ∨ y = (k y (σ x)) := by
          first
          | (have i₁ := b6e575029
             have i₂ := b6e580230
             grind)
          | exact superpose b6e580230 b6e575029
          | exact resolve b6e575029 b6e580230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e575029 b6e580230
        have b6e580653 : y = (k y (σ x)) := by
          first
          | (have r₁ := b6e580499
             have r₂ := b6e66
             grind)
          | exact resolve b6e580499 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580499
        have b6e581720 : (τ (M.op y x)) = (k x (τ x)) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e449401
             have i₂ := b6e580249 x
             grind)
          | exact superpose b6e580249 b6e449401
          | exact resolve b6e449401 b6e580249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e449401
        have b6e581725 : (τ (M.op y x)) = (k y (τ x)) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e444167 y
             have i₂ := b6e580249 x
             grind)
          | exact superpose b6e580249 b6e444167
          | exact resolve b6e444167 b6e580249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e444167
        have b6e582176 : (τ (M.op y x)) = (k y (τ x)) := by
          first
          | (have r₁ := b6e581725
             have r₂ := b6e21
             grind)
          | exact resolve b6e581725 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e581725
        have b6e582181 : (τ (M.op y x)) = (k x (τ x)) := by
          first
          | (have r₁ := b6e581720
             have r₂ := b6e21
             grind)
          | exact resolve b6e581720 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e581720
        have b6e582402 : (τ y) = (k y (τ x)) := by
          first
          | (have i₁ := b6e582176
             have i₂ := b6e1141
             grind)
          | exact superpose b6e1141 b6e582176
          | exact resolve b6e582176 b6e1141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e582176
        have b6e582405 : (τ y) = (k x (τ x)) := by
          first
          | (have i₁ := b6e582181
             have i₂ := b6e1141
             grind)
          | exact superpose b6e1141 b6e582181
          | exact resolve b6e582181 b6e1141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1141 b6e582181
        have b6e582710 : (σ (τ y)) = (k (σ y) x) := by
          first
          | (have i₁ := b6e28 x y
             have i₂ := b6e582402
             grind)
          | exact superpose b6e582402 b6e28
          | exact resolve b6e28 b6e582402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e582402
        have b6e582800 : y = (k (σ y) x) := by
          first
          | (have i₁ := b6e582710
             have i₂ := b6e14 y
             grind)
          | exact superpose b6e14 b6e582710
          | exact resolve b6e582710 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e582710
        have b6e583272 : x = (τ y) ∨ (k x (σ x)) = (k y (σ x)) := by
          first
          | (have i₁ := b6e555763 x
             have i₂ := b6e582405
             grind)
          | exact superpose b6e582405 b6e555763
          | (have j0 := b6e555763 x
             grind)
          | exact resolve b6e555763 b6e582405
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e555763 b6e582405
        have b6e583370 : y = (k x (σ x)) ∨ x = (τ y) := by
          first
          | (have i₁ := b6e583272
             have i₂ := b6e580653
             grind)
          | exact superpose b6e580653 b6e583272
          | exact resolve b6e583272 b6e580653
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580653 b6e583272
        have b6e585959 : y = (M.op x (σ x)) ∨ x = y ∨ x = (τ y) := by
          first
          | (have i₁ := b6e46599 x
             have i₂ := b6e583370
             grind)
          | exact superpose b6e583370 b6e46599
          | exact resolve b6e46599 b6e583370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46599 b6e583370
        have b6e586064 : y = (M.op x (σ x)) ∨ x = (τ y) := by
          first
          | (have r₁ := b6e585959
             have r₂ := b6e67
             grind)
          | exact resolve b6e585959 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e585959
        have b6e586804 : y = (k x y) ∨ y = (M.op x y) ∨ x = (τ y) := by
          first
          | (have i₁ := b6e2985 (σ x)
             have i₂ := b6e586064
             grind)
          | exact superpose b6e586064 b6e2985
          | exact resolve b6e2985 b6e586064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2985 b6e586064
        have b6e586908 : y = (M.op x y) ∨ x = (τ y) := by
          first
          | (have j1 := b6e528135 x
             grind)
          | (have r₁ := b6e586804
             have r₂ := b6e528135 x
             grind)
          | exact resolve b6e586804 b6e528135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e528135 b6e586804
        have b6e586918 : x = (τ y) := by
          first
          | (have r₁ := b6e586908
             have r₂ := b6e20
             grind)
          | exact resolve b6e586908 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e586908
        have b6e587025 : y = (σ x) := by
          first
          | (have i₁ := b6e14 y
             have i₂ := b6e586918
             grind)
          | exact superpose b6e586918 b6e14
          | exact resolve b6e14 b6e586918
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e587030 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e338 y X0
             have i₂ := b6e586918
             grind)
          | exact superpose b6e586918 b6e338
          | exact resolve b6e338 b6e586918
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e338
        have b6e587358 : y ≠ (σ y) := by
          first
          | (have i₁ := b6e66
             have i₂ := b6e587025
             grind)
          | exact superpose b6e587025 b6e66
          | exact resolve b6e66 b6e587025
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e589668 : (τ (k (τ y) y)) = (k (τ (τ x)) x) ∨ (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b6e587030 (τ x)
             have i₂ := b6e557680 y
             grind)
          | exact superpose b6e557680 b6e587030
          | (have j1 := b6e557680 y
             grind)
          | exact resolve b6e587030 b6e557680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e557680
        have b6e589721 : (τ x) = (k (τ x) x) := by
          first
          | (have i₁ := b6e587030 x
             have i₂ := b6e32
             grind)
          | exact superpose b6e32 b6e587030
          | exact resolve b6e587030 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e590082 : (k (τ (τ x)) x) = (k (τ (τ y)) x) ∨ (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b6e589668
             have i₂ := b6e587030 (τ y)
             grind)
          | exact superpose b6e587030 b6e589668
          | exact resolve b6e589668 b6e587030
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e587030 b6e589668
        have b6e590174 : (k (τ (τ x)) x) = (k (τ x) x) ∨ (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b6e590082
             have i₂ := b6e586918
             grind)
          | exact superpose b6e586918 b6e590082
          | exact resolve b6e590082 b6e586918
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e586918 b6e590082
        have b6e590214 : (τ x) = (k (τ (τ x)) x) ∨ (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b6e590174
             have i₂ := b6e589721
             grind)
          | exact superpose b6e589721 b6e590174
          | exact resolve b6e590174 b6e589721
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e589721 b6e590174
        have b6e590244 : y = (σ y) ∨ (τ x) = (k (τ (τ x)) x) := by
          first
          | (have i₁ := b6e590214
             have i₂ := b6e582800
             grind)
          | exact superpose b6e582800 b6e590214
          | exact resolve b6e590214 b6e582800
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e582800 b6e590214
        have b6e590262 : (τ x) = (k (τ (τ x)) x) := by
          first
          | (have r₁ := b6e590244
             have r₂ := b6e587358
             grind)
          | exact resolve b6e590244 b6e587358
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590244
        have b6e590499 : (σ (τ x)) = (k (τ x) (σ x)) := by
          first
          | (have i₁ := b6e27 (τ x) x
             have i₂ := b6e590262
             grind)
          | exact superpose b6e590262 b6e27
          | exact resolve b6e27 b6e590262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590262
        have b6e590638 : (σ (τ x)) = (k (τ x) y) := by
          first
          | (have i₁ := b6e590499
             have i₂ := b6e587025
             grind)
          | exact superpose b6e587025 b6e590499
          | exact resolve b6e590499 b6e587025
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590499
        have b6e590676 : x = (k (τ x) y) := by
          first
          | (have i₁ := b6e590638
             have i₂ := b6e14 x
             grind)
          | exact superpose b6e14 b6e590638
          | exact resolve b6e590638 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590638
        have b6e590754 : (σ x) = (k x (σ y)) := by
          first
          | (have i₁ := b6e27 x y
             have i₂ := b6e590676
             grind)
          | exact superpose b6e590676 b6e27
          | exact resolve b6e27 b6e590676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e590784 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (τ x)) X0) ∨ (σ x) = (σ (τ x)) := by
          intro X0
          first
          | (have i₁ := b6e32393 (τ x) x
             have i₂ := b6e590676
             grind)
          | exact superpose b6e590676 b6e32393
          | exact resolve b6e32393 b6e590676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32393 b6e590676
        have b6e590931 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ (σ x) = (σ (τ x)) := by
          intro X0
          first
          | (have i₁ := b6e590784 X0
             have i₂ := b6e14 x
             grind)
          | exact superpose b6e14 b6e590784
          | exact resolve b6e590784 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590784
        have b6e590944 : y = (k x (σ y)) := by
          first
          | (have i₁ := b6e590754
             have i₂ := b6e587025
             grind)
          | exact superpose b6e587025 b6e590754
          | exact resolve b6e590754 b6e587025
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590754
        have b6e590978 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) ∨ (σ x) = (σ (τ x)) := by
          intro X0
          first
          | (have i₁ := b6e590931 X0
             have i₂ := b6e75 X0
             grind)
          | exact superpose b6e75 b6e590931
          | exact resolve b6e590931 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75 b6e590931
        have b6e590993 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ x) = (σ (τ x)) := by
          intro X0
          first
          | (have i₁ := b6e590978 X0
             have i₂ := b6e580249 X0
             grind)
          | exact superpose b6e580249 b6e590978
          | exact resolve b6e590978 b6e580249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580249 b6e590978
        have b6e591003 : ∀ X0 : G, x = (σ x) ∨ (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e590993 X0
             have i₂ := b6e14 x
             grind)
          | exact superpose b6e14 b6e590993
          | (have j0 := b6e590993 X0
             grind)
          | exact resolve b6e590993 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590993
        have b6e591007 : ∀ X0 : G, x = y ∨ (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e591003 X0
             have i₂ := b6e587025
             grind)
          | exact superpose b6e587025 b6e591003
          | (have j0 := b6e591003 X0
             grind)
          | exact resolve b6e591003 b6e587025
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e587025 b6e591003
        have b6e591010 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b6e591007 X0
             grind)
          | (have r₁ := b6e591007 X0
             have r₂ := b6e67
             grind)
          | exact resolve b6e591007 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e591007
        have b6e591020 : y = (M.op x (σ y)) ∨ x = (k x (σ y)) := by
          first
          | (have i₁ := b6e590944
             have i₂ := b6e32505 x
             grind)
          | exact superpose b6e32505 b6e590944
          | (have j1 := b6e32505 x
             grind)
          | exact resolve b6e590944 b6e32505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32505
        have b6e591259 : y = (M.op y (σ y)) ∨ x = (k x (σ y)) := by
          first
          | (have i₁ := b6e591020
             have i₂ := b6e591010 (σ y)
             grind)
          | exact superpose b6e591010 b6e591020
          | exact resolve b6e591020 b6e591010
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e591010 b6e591020
        have b6e591307 : y = (σ y) ∨ x = (k x (σ y)) := by
          first
          | (have i₁ := b6e591259
             have i₂ := b6e580214
             grind)
          | exact superpose b6e580214 b6e591259
          | exact resolve b6e591259 b6e580214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580214 b6e591259
        have b6e591338 : x = (k x (σ y)) := by
          first
          | (have r₁ := b6e591307
             have r₂ := b6e587358
             grind)
          | exact resolve b6e591307 b6e587358
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e587358 b6e591307
        have b6e591362 : x = y := by
          first
          | (have i₁ := b6e591338
             have i₂ := b6e590944
             grind)
          | exact superpose b6e590944 b6e591338
          | exact resolve b6e591338 b6e590944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590944 b6e591338
        have b6e591376 : False := by grind
        exact b6e591376
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e49 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e52 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e49
          have b7e55 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e52
               have r₂ := b7e23
               grind)
            | exact resolve b7e52 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e56 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e55
            | exact resolve b7e55 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e59 : (τ (σ y)) = (k x y) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e14
            | exact resolve b7e14 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : y = (k x y) := by
            first
            | (have i₁ := b7e59
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e59
            | exact resolve b7e59 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e78 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e60
               grind)
            | exact superpose b7e60 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e79 : y = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b7e78
          have b7e81 : x = (M.op y x) := by
            first
            | (have r₁ := b7e79
               have r₂ := b7e21
               grind)
            | exact resolve b7e79 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e83 : False := by grind
          exact b7e83
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
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e137 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e24
            | (have j1 := b8e62 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e62 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e62 y x
               grind)
            | exact resolve b8e24 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e149 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e137
          have b8e158 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e149
               have r₂ := b8e23
               grind)
            | exact resolve b8e149 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e149
          have b8e165 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e158
               grind)
            | exact superpose b8e158 b8e20
            | exact resolve b8e20 b8e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158
          have b8e271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e165
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e165
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e165 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165
          have b8e272 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e271
          have b8e273 : y = (M.op x y) := by
            first
            | (have r₁ := b8e272
               have r₂ := b8e22
               grind)
            | exact resolve b8e272 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272
          have b8e274 : False := by grind
          exact b8e274

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation3888 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b0e44 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
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
      have b0e45 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have j0 := b0e44 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e46 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e43 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e85 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e46 (σ X0)
           grind)
        | exact superpose b0e46 b0e17
        | exact resolve b0e17 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e88 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e85 X0
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e85
        | exact resolve b0e85 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e85
      have b0e244 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e88 y
           grind)
        | exact superpose b0e88 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e88 y
           grind)
        | exact resolve b0e18 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e255 : False := by grind
      exact b0e255
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e38 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
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
        have b1e39 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b1e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e42 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 X0 (σ y)
             grind)
          | (have r₁ := b1e16 X0 (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e42 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e47 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e45 X0
             have j1 := b1e15 X0 (σ y)
             grind)
          | (have r₁ := b1e45 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e45 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e84 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 y
             have i₂ := b1e47 (σ X0)
             grind)
          | exact superpose b1e47 b1e18
          | exact resolve b1e18 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e505 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e84 x
             grind)
          | exact superpose b1e84 b1e19
          | exact resolve b1e19 b1e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e529 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e505
             have i₂ := b1e39 y
             grind)
          | exact superpose b1e39 b1e505
          | exact resolve b1e505 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e505
        have b1e530 : False := by grind
        exact b1e530
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X0) ≠ X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X1) = (k X2 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 X2 X1
             have i₂ := b2e12 X1 X0
             grind)
          | exact superpose b2e12 b2e16
          | (have j0 := b2e16 X2 X1
             grind)
          | exact resolve b2e16 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X0) ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e38 X0 X1 X2
             have j1 := b2e15 X2 X1
             grind)
          | (have r₁ := b2e38 X0 X1 X0
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e38 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e55 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X2 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e55 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e301 : ∀ X0 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X2
          first
          | (have i₁ := b2e40 x X0 X2
             have i₂ := b2e12 X0 x
             grind)
          | exact superpose b2e12 b2e40
          | (have j0 := b2e40 X0 X0 X2
             grind)
          | exact resolve b2e40 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e673 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e66 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e674 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e673 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e673
        have b2e681 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e674 X0
             have j1 := b2e301 X0 X0
             grind)
          | (have r₁ := b2e674 X0
             have r₂ := b2e301 X0 x
             grind)
          | exact resolve b2e674 b2e301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e301 b2e674
        have b2e691 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e681 (σ X0)
             grind)
          | exact superpose b2e681 b2e18
          | exact resolve b2e18 b2e681
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e700 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e691 X0
             have i₂ := b2e681 X0
             grind)
          | exact superpose b2e681 b2e691
          | exact resolve b2e691 b2e681
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e681 b2e691
        have b2e831 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e700 x
             grind)
          | exact superpose b2e700 b2e21
          | exact resolve b2e21 b2e700
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e700
        have b2e862 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e831
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e831
          | exact resolve b2e831 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e831
        have b2e863 : False := by grind
        exact b2e863
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e37 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b3e40 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e43 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e46 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e44 X0
             have j1 := b3e15 X0 y
             grind)
          | (have r₁ := b3e44 X0
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e44 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e75 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e40 (σ X0)
             grind)
          | exact superpose b3e40 b3e18
          | exact resolve b3e18 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e187 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e75 y
             grind)
          | exact superpose b3e75 b3e19
          | exact resolve b3e19 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e204 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e187
             have i₂ := b3e46 x
             grind)
          | exact superpose b3e46 b3e187
          | exact resolve b3e187 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e187
        have b3e205 : False := by grind
        exact b3e205
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e54 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 X0 (σ y)
               grind)
            | (have r₁ := b4e17 X0 (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e55 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 X0 y
               grind)
            | (have r₁ := b4e17 X0 y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e56 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b4e55 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e57 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b4e54 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e58 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b4e56 X0
               have j1 := b4e16 X0 y
               grind)
            | (have r₁ := b4e56 X0
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e56 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e59 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b4e57 X0
               have j1 := b4e16 X0 (σ y)
               grind)
            | (have r₁ := b4e57 X0
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e57 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e101 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 y
               have i₂ := b4e59 (σ X0)
               grind)
            | exact superpose b4e59 b4e19
            | exact resolve b4e19 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e103 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e101 X0
               have i₂ := b4e58 X0
               grind)
            | exact superpose b4e58 b4e101
            | exact resolve b4e101 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58 b4e101
          have b4e297 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e103 x
               grind)
            | exact superpose b4e103 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e103 x
               grind)
            | exact resolve b4e20 b4e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103
          have b4e308 : False := by grind
          exact b4e308
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
            intro X0 X1
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e49 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X0) ≠ X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X2 X1
               have i₂ := b5e13 X1 X0
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 X2 X1
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X0) ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e49 X0 X1 X2
               have j1 := b5e16 X2 X1
               grind)
            | (have r₁ := b5e49 X0 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e49 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X2 X0
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e66 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e319 : ∀ X0 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X2
            first
            | (have i₁ := b5e51 x X0 X2
               have i₂ := b5e13 X0 x
               grind)
            | exact superpose b5e13 b5e51
            | (have j0 := b5e51 X0 X0 X2
               grind)
            | exact resolve b5e51 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e729 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e78 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e730 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e729 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e729
          have b5e737 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e730 X0
               have j1 := b5e319 X0 X0
               grind)
            | (have r₁ := b5e730 X0
               have r₂ := b5e319 X0 x
               grind)
            | exact resolve b5e730 b5e319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e319 b5e730
          have b5e747 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e737 (σ X0)
               grind)
            | exact superpose b5e737 b5e19
            | exact resolve b5e19 b5e737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e758 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e747 X0
               have i₂ := b5e737 X0
               grind)
            | exact superpose b5e737 b5e747
            | exact resolve b5e747 b5e737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e737 b5e747
          have b5e900 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e758 y
               grind)
            | exact superpose b5e758 b5e24
            | exact resolve b5e24 b5e758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e758
          have b5e930 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e900
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e900
            | exact resolve b5e900 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e900
          have b5e931 : False := by grind
          exact b5e931
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e34 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b6e36 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e34 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e38 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e36 (σ X0)
             grind)
          | exact superpose b6e36 b6e18
          | exact resolve b6e18 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e139 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e38 x
             grind)
          | exact superpose b6e38 b6e22
          | exact resolve b6e22 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e182 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e139
             grind)
          | exact superpose b6e139 b6e13
          | exact resolve b6e13 b6e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139
        have b6e184 : x = (k x x) := by
          first
          | (have i₁ := b6e182
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e182
          | exact resolve b6e182 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e182
        have b6e219 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e184
             grind)
          | exact superpose b6e184 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e184
        have b6e220 : x = (M.op x x) := by grind
        clear b6e219
        have b6e222 : False := by grind
        exact b6e222
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e44 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
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
          have b7e46 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e44 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e46 (σ X0)
               grind)
            | exact superpose b7e46 b7e19
            | exact resolve b7e19 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e154 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e48 y
               grind)
            | exact superpose b7e48 b7e24
            | exact resolve b7e24 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e207 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e154
               grind)
            | exact superpose b7e154 b7e14
            | exact resolve b7e14 b7e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e154
          have b7e209 : y = (k y y) := by
            first
            | (have i₁ := b7e207
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e207
            | exact resolve b7e207 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e207
          have b7e237 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e209
               grind)
            | exact superpose b7e209 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e209
          have b7e238 : y = (M.op y y) := by grind
          clear b7e237
          have b7e240 : False := by grind
          exact b7e240
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e78 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
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
          have b8e86 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b8e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e127 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e86 (σ X0)
               grind)
            | exact superpose b8e86 b8e19
            | (have j1 := b8e86 (σ X0)
               grind)
            | exact resolve b8e19 b8e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e6666 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e127 y
               grind)
            | exact superpose b8e127 b8e24
            | (have j1 := b8e127 y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e127 y
               grind)
            | exact resolve b8e24 b8e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e6714 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
          clear b8e6666
          have b8e6817 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6714
               grind)
            | exact superpose b8e6714 b8e20
            | exact resolve b8e20 b8e6714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6714
          have b8e7007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e6817
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e6817
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e6817 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6817
          have b8e7020 : y = (M.op y y) ∨ x = (M.op x x) := by grind
          clear b8e7007
          have b8e7025 : x = (M.op x x) := by
            first
            | (have r₁ := b8e7020
               have r₂ := b8e22
               grind)
            | exact resolve b8e7020 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7020
          have b8e7026 : False := by grind
          exact b8e7026

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3888 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e37 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e38 : (M.op x y) = (k x y) := by grind
      have b0e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
      have b0e41 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e40
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e40
        | exact resolve b0e40 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e40
      have b0e42 : False := by grind
      exact b0e42
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e36 : (M.op x y) = (k x y) := by grind
        have b1e69 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e82 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e69
             have r₂ := b1e21
             grind)
          | exact resolve b1e69 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e83 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e82
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e82
          | exact resolve b1e82 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82
        have b1e84 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
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
        have b1e85 : False := by grind
        exact b1e85
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e48 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e73 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e497 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e73 X0
             have i₂ := b2e48 X0 X1
             grind)
          | (have i₁ := b2e73 X0
             have i₂ := b2e48 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e48 b2e73
          | (have j1 := b2e48 X1 X0
             grind)
          | exact resolve b2e73 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e73
        have b2e523 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e497 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e497
        have b2e680 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e523 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e523
        have b2e681 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e680 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e680
        have b2e712 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e681 (σ X0)
             grind)
          | exact superpose b2e681 b2e18
          | exact resolve b2e18 b2e681
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e720 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e712 X0
             have i₂ := b2e681 X0
             grind)
          | exact superpose b2e681 b2e712
          | exact resolve b2e712 b2e681
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e681 b2e712
        have b2e1000 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e720 x
             grind)
          | exact superpose b2e720 b2e21
          | exact resolve b2e21 b2e720
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e720
        have b2e1028 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1000
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1000
          | exact resolve b2e1000 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1000
        have b2e1029 : False := by grind
        exact b2e1029
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e35 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e37 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e35
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e35
          | exact resolve b3e35 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e68 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        have b3e80 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e68
             have r₂ := b3e20
             grind)
          | exact resolve b3e68 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e94 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e19
          | exact resolve b3e19 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e97 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e94
             have i₂ := b3e80
             grind)
          | exact superpose b3e80 b3e94
          | exact resolve b3e94 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80 b3e94
        have b3e98 : False := by grind
        exact b3e98
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e81 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b4e82 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          have b4e94 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e82
               have r₂ := b4e21
               grind)
            | exact resolve b4e82 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e95 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e81
               have r₂ := b4e23
               grind)
            | exact resolve b4e81 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e96 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e95
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e95
            | exact resolve b4e95 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95
          have b4e97 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e96
               have i₂ := b4e94
               grind)
            | exact superpose b4e94 b4e96
            | exact resolve b4e96 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94 b4e96
          have b4e98 : False := by grind
          exact b4e98
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e81 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e84 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e495 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e84 X0
               have i₂ := b5e55 X0 X1
               grind)
            | (have i₁ := b5e84 X0
               have i₂ := b5e55 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e55 b5e84
            | (have j1 := b5e55 X1 X0
               grind)
            | exact resolve b5e84 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e84
          have b5e519 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e495 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e495
          have b5e672 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e519 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e519
          have b5e673 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e672 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e672
          have b5e703 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e673 (σ X0)
               grind)
            | exact superpose b5e673 b5e19
            | exact resolve b5e19 b5e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e711 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e703 X0
               have i₂ := b5e673 X0
               grind)
            | exact superpose b5e673 b5e703
            | exact resolve b5e703 b5e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e673 b5e703
          have b5e989 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e711 y
               grind)
            | exact superpose b5e711 b5e24
            | exact resolve b5e24 b5e711
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e711
          have b5e1016 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e989
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e989
            | exact resolve b5e989 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e989
          have b5e1017 : False := by grind
          exact b5e1017
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e60 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e78 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e81 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e78 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e591 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e81 X0
             have i₂ := b6e60 X0 X1
             grind)
          | (have i₁ := b6e81 X0
             have i₂ := b6e60 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e60 b6e81
          | (have j1 := b6e60 X1 X0
             grind)
          | exact resolve b6e81 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e81
        have b6e613 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e591 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e591
        have b6e774 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e613 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e613
        have b6e775 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e774 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e774
        have b6e839 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e775 (σ X0)
             grind)
          | exact superpose b6e775 b6e18
          | exact resolve b6e18 b6e775
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e846 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e839 X0
             have i₂ := b6e775 X0
             grind)
          | exact superpose b6e775 b6e839
          | exact resolve b6e839 b6e775
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e775 b6e839
        have b6e1122 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e846 x
             grind)
          | exact superpose b6e846 b6e22
          | exact resolve b6e22 b6e846
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e846
        have b6e1308 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e1122
             grind)
          | exact superpose b6e1122 b6e13
          | exact resolve b6e13 b6e1122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1122
        have b6e1309 : y = (M.op x x) := by
          first
          | (have i₁ := b6e1308
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1308
          | exact resolve b6e1308 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1308
        have b6e1315 : False := by grind
        exact b6e1315
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e90 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e93 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e90 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e336 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e93 X0
               have i₂ := b7e59 X0 X1
               grind)
            | (have i₁ := b7e93 X0
               have i₂ := b7e59 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e59 b7e93
            | (have j1 := b7e59 X1 X0
               grind)
            | exact resolve b7e93 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59 b7e93
          have b7e355 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e336 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e336
          have b7e505 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e355 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e355
          have b7e565 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e505 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e505
            | exact resolve b7e505 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e583 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e505 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e505
          have b7e591 : (σ x) = (k (σ y) (σ y)) := by grind
          clear b7e565
          have b7e608 : (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b7e591
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e591
            | exact resolve b7e591 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e591
          have b7e626 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e608
               have i₂ := b7e583 y
               grind)
            | exact superpose b7e583 b7e608
            | exact resolve b7e608 b7e583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e583 b7e608
          have b7e860 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e626
               grind)
            | exact superpose b7e626 b7e14
            | exact resolve b7e14 b7e626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e626
          have b7e861 : x = (M.op y y) := by
            first
            | (have i₁ := b7e860
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e860
            | exact resolve b7e860 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e860
          have b7e866 : False := by grind
          exact b7e866
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e65 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ y) X0
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
          have b8e518 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e65 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e519 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e518
               have r₂ := b8e23
               grind)
            | exact resolve b8e518 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e518
          have b8e520 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e519
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e519
            | exact resolve b8e519 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e519
          have b8e670 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e520
               grind)
            | exact superpose b8e520 b8e20
            | exact resolve b8e20 b8e520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e520
          have b8e758 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e670
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e670
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e670 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e670
          have b8e764 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e758
          have b8e767 : y = (M.op x x) := by
            first
            | (have r₁ := b8e764
               have r₂ := b8e22
               grind)
            | exact resolve b8e764 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e764
          have b8e768 : False := by grind
          exact b8e768

/-- `Equation4486`: `x ◇ (y ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxx_x_pxy_Equation4486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      clear b0e21
      have b0e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X3 (M.op X0 X0)
           have i₂ := b0e11 X3 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e11 X2 X1 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, x = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e35 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e39 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e34 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e38 X1
           grind)
        | exact superpose b0e38 b0e11
        | exact resolve b0e11 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (σ x)
           have i₂ := b0e39 X1
           grind)
        | exact superpose b0e39 b0e11
        | exact resolve b0e11 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e69 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) := by
        intro X1
        first
        | (have i₁ := b0e64 x X1
           have i₂ := b0e42 x X1
           grind)
        | exact superpose b0e42 b0e64
        | exact resolve b0e64 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j1 := b0e16 X2 X2
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
      have b0e85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X0) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e88 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e81 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e132 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e69 (σ y)
           grind)
        | exact superpose b0e69 b0e18
        | exact resolve b0e18 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e172 : ∀ X0 X2 : G, (M.op x X0) = (M.op (M.op X0 X2) X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e11 x X0 X2
           have i₂ := b0e42 x X0
           grind)
        | exact superpose b0e42 b0e11
        | exact resolve b0e11 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e176 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op x X0) ∨ (M.op x X0) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (M.op X1 X1) X1
           have i₂ := b0e42 (M.op X1 X1) X1
           grind)
        | exact superpose b0e42 b0e14
        | (have r₁ := b0e14 (M.op x x) X1
           have r₂ := b0e42 (M.op x x) x
           grind)
        | exact resolve b0e14 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e177 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X0)) = (M.op (M.op (M.op X0 X0) X2) (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 (M.op X0 X0) X2
           have i₂ := b0e42 (M.op X0 X0) X0
           grind)
        | exact superpose b0e42 b0e11
        | exact resolve b0e11 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e184 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e177 X0 X1 x
           have i₂ := b0e42 (M.op (M.op X0 X0) x) X0
           grind)
        | exact superpose b0e42 b0e177
        | exact resolve b0e177 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e177
      have b0e319 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X3 X3) = X3 ∨ (k X3 X0) = (M.op X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e36 X0 X1 X2
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e36
        | (have j1 := b0e16 X3 X3
           grind)
        | exact resolve b0e36 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e741 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X2) = (M.op X1 (M.op X2 X2)) ∨ (M.op X3 X3) = X3 ∨ (k X3 X0) = (M.op X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e32 X0 X0 X1 X2
           have i₂ := b0e16 X3 X0
           grind)
        | exact superpose b0e16 b0e32
        | (have j1 := b0e16 X3 X3
           grind)
        | exact resolve b0e32 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e922 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X0) X2) = (M.op x X2) ∨ (M.op X3 X3) = X3 ∨ (k X3 X0) = (M.op X3 X0) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e741 X0 x X2 X3
           have i₂ := b0e42 x X2
           grind)
        | exact superpose b0e42 b0e741
        | (have j0 := b0e741 X0 x X2 X3
           grind)
        | exact resolve b0e741 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e741
      have b0e1348 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
      have b0e1897 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X2 X3) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e14 X2 X1
           have i₂ := b0e88 X0 X1 X2
           grind)
        | exact superpose b0e88 b0e14
        | (have j1 := b0e88 X2 X3 X0
           grind)
        | (have r₁ := b0e14 X2 X1
           have r₂ := b0e88 X0 X1 X2
           grind)
        | exact resolve b0e14 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e1939 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = X0 ∨ (k X2 X3) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e1897 X0 X1 X2 X3
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1897
      have b0e6301 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e85 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85
      have b0e6302 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e6301 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6301
      have b0e11436 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e1939 X0 X1 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1939
      have b0e11439 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e11436 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11436
      have b0e14166 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X3 X3) = X3 ∨ (k X3 X1) = (M.op X3 X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e184 X0 X1
           have i₂ := b0e319 X0 x X2 X3
           grind)
        | (have i₁ := b0e184 X0 X1
           have i₂ := b0e319 X0 X1 x X3
           grind)
        | exact superpose b0e319 b0e184
        | (have j1 := b0e319 X1 X1 X2 X3
           grind)
        | exact resolve b0e184 b0e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e184 b0e319
      have b0e23745 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e922 X0 x (M.op X0 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e922
      have b0e23769 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e23745 X0
           have j1 := b0e14166 X0 X0 (M.op X0 X0) (M.op X0 X0)
           grind)
        | (have r₁ := b0e23745 x
           have r₂ := b0e14166 x x x x
           grind)
        | exact resolve b0e23745 b0e14166
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14166 b0e23745
      have b0e23875 : ∀ X0 : G, (M.op X0 X0) = (M.op x X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have i₁ := b0e23769 X0
           have i₂ := b0e42 (M.op X0 X0) X0
           grind)
        | exact superpose b0e42 b0e23769
        | (have j0 := b0e23769 X0
           grind)
        | exact resolve b0e23769 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e23769
      have b0e23927 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e23875 X0
           have i₂ := b0e172 X0 X0
           grind)
        | exact superpose b0e172 b0e23875
        | (have j0 := b0e23875 X0
           grind)
        | exact resolve b0e23875 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e172 b0e23875
      have b0e23936 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e23927 X0
           have j1 := b0e176 X0 X0
           grind)
        | (have r₁ := b0e23927 X0
           have r₂ := b0e176 X0 x
           grind)
        | (have r₁ := b0e23927 x
           have r₂ := b0e176 x x
           grind)
        | exact resolve b0e23927 b0e176
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e176 b0e23927
      have b0e24114 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op x (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e22 X0 (M.op (τ X0) (τ X0))
           have i₂ := b0e23936 (τ X0)
           grind)
        | exact superpose b0e23936 b0e22
        | exact resolve b0e22 b0e23936
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e49785 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e26 X0 X1
           have i₂ := b0e11439 X0 (σ X1)
           grind)
        | exact superpose b0e11439 b0e26
        | (have j1 := b0e11439 (τ X0) X1
           grind)
        | exact resolve b0e26 b0e11439
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e11439
      have b0e117175 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e6302 (τ X0)
           have i₂ := b0e49785 X0 (τ X0)
           grind)
        | exact superpose b0e49785 b0e6302
        | (have j0 := b0e6302 (τ X0)
           have j1 := b0e49785 X0 x
           grind)
        | exact resolve b0e6302 b0e49785
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6302 b0e49785
      have b0e117383 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e117175 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117175
      have b0e117413 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e117383 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e117383
        | (have j0 := b0e117383 X0
           grind)
        | exact resolve b0e117383 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117383
      have b0e117424 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e117413 X0
           have j1 := b0e14 X0 X0
           grind)
        | (have r₁ := b0e117413 X0
           have r₂ := b0e14 X0 x
           grind)
        | exact resolve b0e117413 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117413
      have b0e120143 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e1348 X0 X0
           have i₂ := b0e117424 (τ X0)
           grind)
        | exact superpose b0e117424 b0e1348
        | exact resolve b0e1348 b0e117424
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1348
      have b0e120194 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e120143 X0
           have i₂ := b0e117424 X0
           grind)
        | exact superpose b0e117424 b0e120143
        | exact resolve b0e120143 b0e117424
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117424 b0e120143
      have b0e122782 : ∀ X0 : G, (σ (M.op x (τ X0))) = (k (σ (τ (M.op X0 X0))) X0) := by
        intro X0
        first
        | (have i₁ := b0e24114 X0
           have i₂ := b0e120194 X0
           grind)
        | exact superpose b0e120194 b0e24114
        | exact resolve b0e24114 b0e120194
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24114 b0e120194
      have b0e123086 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op x (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e122782 X0
           have i₂ := b0e13 (M.op X0 X0)
           grind)
        | exact superpose b0e13 b0e122782
        | exact resolve b0e122782 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e122782
      have b0e123143 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e123086 X0
           have i₂ := b0e23936 X0
           grind)
        | exact superpose b0e23936 b0e123086
        | exact resolve b0e123086 b0e23936
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23936 b0e123086
      have b0e128086 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e123143 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e123143
        | exact resolve b0e123143 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123143
      have b0e129391 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e132
           have i₂ := b0e128086 y
           grind)
        | exact superpose b0e128086 b0e132
        | (have r₁ := b0e132
           have r₂ := b0e128086 y
           grind)
        | exact resolve b0e132 b0e128086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132 b0e128086
      have b0e129444 : False := by grind
      exact b0e129444
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b1e47 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have r₁ := b1e15 x x
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e47 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e85 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
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
        have b1e88 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e85 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85
        have b1e141 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e24 X0 x
             have i₂ := b1e48 (τ X0)
             grind)
          | exact superpose b1e48 b1e24
          | exact resolve b1e24 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e48
        have b1e998 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e141 (σ x)
             have i₂ := b1e88 (σ x)
             grind)
          | exact superpose b1e88 b1e141
          | (have j1 := b1e88 (σ x)
             grind)
          | exact resolve b1e141 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88 b1e141
        have b1e1003 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e998
        have b1e1007 : False := by grind
        exact b1e1007
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b2e29 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e29 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e43 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x x
             have i₂ := b2e34 x
             grind)
          | exact superpose b2e34 b2e15
          | (have r₁ := b2e15 x x
             have r₂ := b2e34 x
             grind)
          | exact resolve b2e15 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e44 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e91 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
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
        have b2e96 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b2e91 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e167 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 x
             have i₂ := b2e44 (τ X0)
             grind)
          | exact superpose b2e44 b2e24
          | exact resolve b2e24 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e44
        have b2e841 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e167 (σ x)
             have i₂ := b2e96 (σ x)
             grind)
          | exact superpose b2e96 b2e167
          | (have j1 := b2e96 (σ x)
             grind)
          | exact resolve b2e167 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96 b2e167
        have b2e844 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e841
        have b2e848 : False := by grind
        exact b2e848
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e46 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e93 : ∀ X0 : G, (σ x) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e49 (σ X0)
             grind)
          | exact superpose b3e49 b3e18
          | exact resolve b3e18 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e125 : ∀ X0 : G, (k x X0) = (τ (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e13 (k x X0)
             have i₂ := b3e93 X0
             grind)
          | exact superpose b3e93 b3e13
          | exact resolve b3e13 b3e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93
        have b3e126 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e125 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e125
          | exact resolve b3e125 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e125
        have b3e136 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x x) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e17 x X0
             have i₂ := b3e126 X0
             grind)
          | exact superpose b3e126 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e126
        have b3e137 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e136 X0
             grind)
          | (have r₁ := b3e136 x
             have r₂ := b3e20
             grind)
          | (have r₁ := b3e136 X0
             have r₂ := b3e20
             grind)
          | exact resolve b3e136 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e136
        have b3e10489 : x ≠ x ∨ x = (M.op x x) := by
          first
          | (have j0 := b3e137 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e137
        have b3e10490 : x = (M.op x x) := by grind
        clear b3e10489
        have b3e10502 : False := by grind
        exact b3e10502
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e38 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
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
          have b4e42 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e39 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e43 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e38 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e38
            | exact resolve b4e38 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e70 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e43 (σ x)
               grind)
            | exact superpose b4e43 b4e20
            | exact resolve b4e20 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e73 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e42 x
               grind)
            | exact superpose b4e42 b4e70
            | exact resolve b4e70 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e70
          have b4e74 : False := by grind
          exact b4e74
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b5e35 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e35 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e49 : ∀ X0 : G, y ≠ y ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e16 y x
               have i₂ := b5e40 y
               grind)
            | exact superpose b5e40 b5e16
            | (have r₁ := b5e16 y x
               have r₂ := b5e40 y
               grind)
            | exact resolve b5e16 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e50 : ∀ X0 : G, y = (k y X0) := by
            intro X0
            first
            | (have j0 := b5e49 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e98 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
          have b5e102 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e98 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e141 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e26 X0 y
               have i₂ := b5e50 (τ X0)
               grind)
            | exact superpose b5e50 b5e26
            | exact resolve b5e26 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e50
          have b5e781 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e141 (σ y)
               have i₂ := b5e102 (σ y)
               grind)
            | exact superpose b5e102 b5e141
            | (have j1 := b5e102 (σ y)
               grind)
            | exact resolve b5e141 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102 b5e141
          have b5e784 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e781
          have b5e788 : False := by grind
          exact b5e788
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e29 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e29 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e29
          | exact resolve b6e29 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) x
             have i₂ := b6e34 (σ x)
             grind)
          | exact superpose b6e34 b6e15
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e34 (σ x)
             grind)
          | exact resolve b6e15 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e44 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e47 : ∀ X0 : G, (σ x) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e44 (σ X0)
             grind)
          | exact superpose b6e44 b6e18
          | exact resolve b6e18 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e55 : ∀ X0 : G, (k x X0) = (τ (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e13 (k x X0)
             have i₂ := b6e47 X0
             grind)
          | exact superpose b6e47 b6e13
          | exact resolve b6e13 b6e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e56 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b6e55 X0
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e55
          | exact resolve b6e55 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e84 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x x) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e17 x X0
             have i₂ := b6e56 X0
             grind)
          | exact superpose b6e56 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e85 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e84 X0
             grind)
          | (have r₁ := b6e84 x
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e84 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e84 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e2009 : x ≠ x ∨ x = (M.op x x) := by
          first
          | (have j0 := b6e85 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e2010 : x = (M.op x x) := by grind
        clear b6e2009
        have b6e2015 : False := by grind
        exact b6e2015
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e35 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e35 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e50 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) x
               have i₂ := b7e40 (σ y)
               grind)
            | exact superpose b7e40 b7e16
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e40 (σ y)
               grind)
            | exact resolve b7e16 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e51 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e50 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e59 : ∀ X0 : G, (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e51 (σ X0)
               grind)
            | exact superpose b7e51 b7e19
            | exact resolve b7e19 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e90 : ∀ X0 : G, (k y X0) = (τ (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e14 (k y X0)
               have i₂ := b7e59 X0
               grind)
            | exact superpose b7e59 b7e14
            | exact resolve b7e14 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e91 : ∀ X0 : G, y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b7e90 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e90
            | exact resolve b7e90 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e108 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e18 y X0
               have i₂ := b7e91 X0
               grind)
            | exact superpose b7e91 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e110 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e108 X0
               grind)
            | (have r₁ := b7e108 y
               have r₂ := b7e22
               grind)
            | (have r₁ := b7e108 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e108 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e2515 : y ≠ y ∨ y = (M.op y y) := by
            first
            | (have j0 := b7e110 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e2516 : y = (M.op y y) := by grind
          clear b7e2515
          have b7e2522 : False := by grind
          exact b7e2522
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
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
          have b8e84 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
          have b8e90 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e84 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e338 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e36 X0 X0 X2
               have i₂ := b8e90 X0
               grind)
            | exact superpose b8e90 b8e36
            | (have j1 := b8e90 X0
               grind)
            | exact resolve b8e36 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e18260 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e338 (σ x) (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e338 (σ x) X0 (σ x)
               grind)
            | exact superpose b8e338 b8e23
            | (have j1 := b8e338 (σ x) x x
               grind)
            | exact resolve b8e23 b8e338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e18288 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 (σ y)) = (M.op X1 (σ y)) ∨ (k X1 (σ y)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e90 X1
               have i₂ := b8e338 X1 X1 X0
               grind)
            | (have i₁ := b8e90 X1
               have i₂ := b8e338 X1 X0 X1
               grind)
            | exact superpose b8e338 b8e90
            | (have j0 := b8e90 X1
               have j1 := b8e338 X1 X1 x
               grind)
            | exact resolve b8e90 b8e338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90 b8e338
          have b8e18529 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 (σ y)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b8e18288 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18288
          have b8e18550 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b8e18529 x (σ x)
               grind)
            | (have r₁ := b8e18260 x
               have r₂ := b8e18529 x (σ x)
               grind)
            | exact resolve b8e18260 b8e18529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18260 b8e18529
          have b8e18554 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e18550
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e18550
            | exact resolve b8e18550 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18550
          have b8e23473 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e18554
               grind)
            | exact superpose b8e18554 b8e20
            | exact resolve b8e20 b8e18554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18554
          have b8e24378 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e23473
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e23473
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e23473 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23473
          have b8e24392 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e24378
          have b8e24399 : y = (M.op y y) := by
            first
            | (have r₁ := b8e24392
               have r₂ := b8e21
               grind)
            | exact resolve b8e24392 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24392
          have b8e24400 : False := by grind
          exact b8e24400

/-- `Equation4506`: `x ◇ (y ◇ z) = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4506 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X0) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e34 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e11 X0 X3 X4
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 (M.op X0 X0) X0
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e15
        | (have j0 := b0e15 (M.op X0 X0) X0
           grind)
        | (have r₁ := b0e15 X0 (M.op (M.op X0 X0) X0)
           have r₂ := b0e11 X0 (M.op X0 X0) X0
           grind)
        | exact resolve b0e15 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X3
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 X2
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ y)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e74 X0 X1 X2
           have i₂ := b0e34 X1
           grind)
        | exact superpose b0e34 b0e74
        | (have j0 := b0e74 X0 X1 X2
           grind)
        | exact resolve b0e74 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e96 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e99 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e129 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e37 X0 X1 X2 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e37
        | exact resolve b0e37 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e153 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = X4 ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e16 (M.op X0 X1) X4
           have i₂ := b0e37 (M.op X0 X1) X0 X1 X2 X3
           grind)
        | (have i₁ := b0e16 (M.op X0 X1) X4
           have i₂ := b0e37 (M.op X0 X1) X2 X3 X0 X1
           grind)
        | exact superpose b0e37 b0e16
        | (have j0 := b0e16 (M.op X0 X1) X4
           grind)
        | exact resolve b0e16 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e167 : ∀ X0 X1 X4 : G, (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) (σ y)) = X4 ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e153 X0 X1 x x X4
           have i₂ := b0e99 (M.op X0 X1) x x
           grind)
        | exact superpose b0e99 b0e153
        | (have j0 := b0e153 X0 X1 x x X4
           grind)
        | exact resolve b0e153 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e206 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 y) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e129 X1 X2 X2
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e129 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e16 b0e129
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e129 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e209 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e129 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e129
        | exact resolve b0e129 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e299 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e209 (σ x)
           grind)
        | exact superpose b0e209 b0e18
        | exact resolve b0e18 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e449 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e79 X1 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e452 : ∀ X0 X1 : G, (M.op X0 y) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e449 X0 X1
           have i₂ := b0e209 X0
           grind)
        | exact superpose b0e209 b0e449
        | (have j0 := b0e449 X0 X1
           grind)
        | (have r₁ := b0e449 X0 (M.op X0 y)
           have r₂ := b0e209 X0
           grind)
        | exact resolve b0e449 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e449
      have b0e1226 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) ≠ X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = (k (M.op X4 X4) X4) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e52 X4 X0 X1
           have i₂ := b0e70 X4 (M.op X0 X1) X2 X3
           grind)
        | (have i₁ := b0e52 X1 X2 X3
           have i₂ := b0e70 X0 X1 X2 X3
           grind)
        | exact superpose b0e70 b0e52
        | (have j0 := b0e52 X4 X1 X2
           have j1 := b0e70 X4 (M.op X0 X1) X2 X3
           grind)
        | (have r₁ := b0e52 (M.op (M.op X1 X2) (M.op X2 X3)) X1 X2
           have r₂ := b0e70 (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X1 X2) X2 X3
           grind)
        | (have r₁ := b0e52 (M.op X1 X2) X1 X2
           have r₂ := b0e70 (M.op X1 X2) (M.op X1 X2) X2 X3
           grind)
        | exact resolve b0e52 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52 b0e70
      have b0e1238 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) (σ y)) ≠ X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = (k (M.op X4 X4) X4) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e1226 X0 X1 x x X4
           have i₂ := b0e99 (M.op X0 X1) x x
           grind)
        | exact superpose b0e99 b0e1226
        | (have j0 := b0e1226 X0 X1 x x X4
           grind)
        | (have r₁ := b0e1226 X0 X1 X1 x (M.op (M.op X0 X1) (σ y))
           have r₂ := b0e99 (M.op X0 X1) X1 x
           grind)
        | exact resolve b0e1226 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1226
      have b0e1249 : ∀ X0 X1 X4 : G, (M.op (M.op X4 X4) (M.op X4 X4)) = X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = (k (M.op X4 X4) X4) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X4
        first
        | (have j0 := b0e1238 X0 X1 X4
           have j1 := b0e167 X0 X1 X4
           grind)
        | (have r₁ := b0e1238 X0 X1 (k (M.op X0 X1) (σ y))
           have r₂ := b0e167 X0 X1 (σ y)
           grind)
        | (have r₁ := b0e1238 X0 X1 X4
           have r₂ := b0e167 X0 X1 X4
           grind)
        | (have r₁ := b0e1238 X0 X1 (M.op (M.op X0 X1) (σ y))
           have r₂ := b0e167 X0 X1 (M.op (M.op X0 X1) (σ y))
           grind)
        | exact resolve b0e1238 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e167 b0e1238
      have b0e1260 : ∀ X0 X1 X4 : G, (M.op (M.op X4 X4) (σ y)) = X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = (k (M.op X4 X4) X4) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e1249 X0 X1 X4
           have i₂ := b0e99 (M.op X4 X4) X4 X4
           grind)
        | exact superpose b0e99 b0e1249
        | (have j0 := b0e1249 X0 X1 X4
           grind)
        | exact resolve b0e1249 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1249
      have b0e1271 : ∀ X0 X1 X4 : G, (M.op (M.op X4 X4) y) = X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = (k (M.op X4 X4) X4) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e1260 X0 X1 X4
           have i₂ := b0e209 (M.op X4 X4)
           grind)
        | exact superpose b0e209 b0e1260
        | (have j0 := b0e1260 X0 X1 X4
           grind)
        | exact resolve b0e1260 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1260
      have b0e1282 : ∀ X0 X1 X4 : G, (k (M.op X4 X4) X4) = (M.op (M.op X4 X4) (σ y)) ∨ (M.op (M.op X4 X4) y) = X4 ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e1271 X0 X1 X4
           have i₂ := b0e99 (M.op X4 X4) X4 X4
           grind)
        | exact superpose b0e99 b0e1271
        | (have j0 := b0e1271 X0 X1 X4
           grind)
        | exact resolve b0e1271 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99 b0e1271
      have b0e1286 : ∀ X0 X1 X4 : G, (k (M.op X4 X4) X4) = (M.op (M.op X4 X4) y) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X4 X4) y) = X4 ∨ (M.op (M.op X0 X1) X4) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e1282 X0 X1 X4
           have i₂ := b0e209 (M.op X4 X4)
           grind)
        | exact superpose b0e209 b0e1282
        | (have j0 := b0e1282 X0 X1 X4
           grind)
        | exact resolve b0e1282 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1282
      have b0e24065 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) y) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) y) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e1286 X0 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1286
      have b0e24078 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) y) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e24065 X0
           have j1 := b0e452 (M.op X0 X0) X0
           grind)
        | (have r₁ := b0e24065 y
           have r₂ := b0e452 (M.op y y) (k (M.op y y) y)
           grind)
        | (have r₁ := b0e24065 x
           have r₂ := b0e452 (M.op x x) x
           grind)
        | (have r₁ := b0e24065 (M.op X0 y)
           have r₂ := b0e452 X0 (M.op (M.op (M.op X0 y) (M.op X0 y)) y)
           grind)
        | exact resolve b0e24065 b0e452
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e452 b0e24065
      have b0e24103 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e24078 X0
           have j1 := b0e206 X0 x (M.op X0 X0)
           grind)
        | (have r₁ := b0e24078 X0
           have r₂ := b0e206 X0 (M.op X0 X0) x
           grind)
        | (have r₁ := b0e24078 y
           have r₂ := b0e206 y (M.op y y) x
           grind)
        | exact resolve b0e24078 b0e206
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e206 b0e24078
      have b0e24124 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e24103 X0
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e24103
        | (have j0 := b0e24103 X0
           grind)
        | exact resolve b0e24103 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24103
      have b0e24136 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 y) ∨ (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e24124 X0
           have i₂ := b0e209 X0
           grind)
        | exact superpose b0e209 b0e24124
        | (have j0 := b0e24124 X0
           grind)
        | exact resolve b0e24124 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24124
      have b0e24145 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (k (M.op X0 X0) X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e24136 X0
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e24136
        | (have j0 := b0e24136 X0
           grind)
        | exact resolve b0e24136 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e24136
      have b0e24152 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e24145 X0
           have i₂ := b0e209 X0
           grind)
        | exact superpose b0e209 b0e24145
        | (have j0 := b0e24145 X0
           grind)
        | exact resolve b0e24145 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24145
      have b0e26543 : (M.op (σ x) y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e24152 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e24152
        | (have j0 := b0e24152 (σ x)
           grind)
        | exact resolve b0e24152 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e26549 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e24152 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e24152
        | (have j0 := b0e24152 x
           grind)
        | exact resolve b0e24152 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24152
      have b0e26650 : (M.op (σ x) y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e26543
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e26543
        | exact resolve b0e26543 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26543
      have b0e30623 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e26650
           have i₂ := b0e26549
           grind)
        | exact superpose b0e26549 b0e26650
        | exact resolve b0e26650 b0e26549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26549 b0e26650
      have b0e30751 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e30623
           have r₂ := b0e299
           grind)
        | exact resolve b0e30623 b0e299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e299 b0e30623
      have b0e32357 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e35 (σ x) y
           have i₂ := b0e30751
           grind)
        | exact superpose b0e30751 b0e35
        | exact resolve b0e35 b0e30751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e32407 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e32357
           have i₂ := b0e96
           grind)
        | exact superpose b0e96 b0e32357
        | exact resolve b0e32357 b0e96
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96 b0e32357
      have b0e32424 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e32407
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e32407
        | exact resolve b0e32407 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32407
      have b0e32430 : (σ y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e32424
           have i₂ := b0e209 (σ x)
           grind)
        | exact superpose b0e209 b0e32424
        | exact resolve b0e32424 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e209 b0e32424
      have b0e33673 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e30751
           have i₂ := b0e32430
           grind)
        | exact superpose b0e32430 b0e30751
        | exact resolve b0e30751 b0e32430
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30751 b0e32430
      have b0e33716 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
      clear b0e33673
      have b0e33889 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e129 X0 x y
           have i₂ := b0e33716
           grind)
        | exact superpose b0e33716 b0e129
        | exact resolve b0e129 b0e33716
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129
      have b0e34701 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e33716
           have i₂ := b0e33889 x
           grind)
        | exact superpose b0e33889 b0e33716
        | exact resolve b0e33716 b0e33889
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33716 b0e33889
      have b0e34713 : x = (M.op x x) ∨ (σ x) = (σ y) := by grind
      clear b0e34701
      have b0e34727 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e34713
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e34713
        | exact resolve b0e34713 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34713
      have b0e34909 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e34727
           grind)
        | exact superpose b0e34727 b0e12
        | exact resolve b0e12 b0e34727
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34727
      have b0e35012 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e34909
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e34909
        | exact resolve b0e34909 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34909
      have b0e35013 : x = y := by grind
      clear b0e35012
      have b0e37613 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e35013
           grind)
        | exact superpose b0e35013 b0e18
        | exact resolve b0e18 b0e35013
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35013
      have b0e37733 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e37613
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e37613
        | exact resolve b0e37613 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37613
      have b0e37760 : False := by grind
      exact b0e37760
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : y = (k x y) := by grind
        have b1e48 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e51 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e48
        have b1e53 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e51
             have r₂ := b1e21
             grind)
          | exact resolve b1e51 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e56 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e58 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e56
          | exact resolve b1e56 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e56
        have b1e59 : False := by grind
        exact b1e59
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e215 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e59 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e216 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e215
             have r₂ := b2e22
             grind)
          | exact resolve b2e215 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e215
        have b2e217 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e216
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e216
          | exact resolve b2e216 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e216
        have b2e218 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e217
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e217
          | exact resolve b2e217 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e217
        have b2e219 : False := by grind
        exact b2e219
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e25
          | exact resolve b3e25 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e31 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e26
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e32 : y = (k x y) := by
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
        have b3e43 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e44 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e43
        have b3e45 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e44
             have r₂ := b3e20
             grind)
          | exact resolve b3e44 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e47 : y = (M.op x x) := by
          first
          | (have i₁ := b3e45
             have i₂ := b3e32
             grind)
          | exact superpose b3e32 b3e45
          | exact resolve b3e45 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e45
        have b3e48 : False := by grind
        exact b3e48
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X0) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e30 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b5e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b5e27
          have b5e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e13 X0 X3 X4
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e45 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b5e47 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 (M.op X0 X0) X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 (M.op X0 X0) X0
               grind)
            | (have r₁ := b5e17 X0 (M.op (M.op X0 X0) X0)
               have r₂ := b5e13 X0 (M.op X0 X0) X0
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b5e45
          have b5e49 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e57 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e60 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e33
            | exact resolve b5e33 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e83 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e36 X0 X1 X2 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e36
            | exact resolve b5e36 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e102 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) (M.op X2 X3)) = X4 ∨ (M.op (M.op X0 X1) X4) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e18 (M.op X0 X1) X4
               have i₂ := b5e36 (M.op X0 X1) X0 X1 X2 X3
               grind)
            | (have i₁ := b5e18 (M.op X0 X1) X4
               have i₂ := b5e36 (M.op X0 X1) X2 X3 X0 X1
               grind)
            | exact superpose b5e36 b5e18
            | (have j0 := b5e18 (M.op X0 X1) X4
               grind)
            | exact resolve b5e18 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e112 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (M.op X1 y) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e83 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e83 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e83
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e83 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e121 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x x
               have i₂ := b5e83 X0 x x
               grind)
            | exact superpose b5e83 b5e13
            | exact resolve b5e13 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e124 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op (M.op X0 X1) y)) := by
            intro X0 X1
            grind
          have b5e231 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X3 ∨ (k X0 X3) = (M.op X0 X3) ∨ (M.op X0 X3) = X3 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e18 X0 X3
               have i₂ := b5e57 X0 X0 X1 X2
               grind)
            | (have i₁ := b5e18 (M.op X2 X3) X1
               have i₂ := b5e57 X0 (M.op X2 X3) X2 X3
               grind)
            | exact superpose b5e57 b5e18
            | (have j0 := b5e18 X0 X0
               have j1 := b5e57 X3 X0 X2 X3
               grind)
            | exact resolve b5e18 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e266 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e57 X0 X0 X2 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e270 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e266 X0 x x
               have i₂ := b5e83 X0 x x
               grind)
            | exact superpose b5e83 b5e266
            | (have j0 := b5e266 X0 x x
               grind)
            | exact resolve b5e266 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e266
          have b5e290 : ∀ X0 X3 : G, (k X0 X3) = (M.op X0 X3) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X3) = X3 ∨ (M.op X0 y) = X3 ∨ (M.op X0 X0) = X0 := by
            intro X0 X3
            first
            | (have i₁ := b5e231 X0 x x X3
               have i₂ := b5e83 X0 x x
               grind)
            | exact superpose b5e83 b5e231
            | (have j0 := b5e231 X0 x x X3
               grind)
            | exact resolve b5e231 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e231
          have b5e388 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e60 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e391 : ∀ X0 X1 : G, (M.op X0 y) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e388 X0 X1
               have i₂ := b5e121 X0
               grind)
            | exact superpose b5e121 b5e388
            | (have j0 := b5e388 X0 X1
               grind)
            | (have r₁ := b5e388 X0 (M.op X0 y)
               have r₂ := b5e121 X0
               grind)
            | (have r₁ := b5e388 y (M.op (M.op (M.op y y) (M.op y y)) (M.op y y))
               have r₂ := b5e121 (M.op y y)
               grind)
            | exact resolve b5e388 b5e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e388
          have b5e667 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e873 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) ≠ X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = (k (M.op X4 X4) X4) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e47 X4 X0 X1
               have i₂ := b5e57 X4 (M.op X0 X1) X2 X3
               grind)
            | (have i₁ := b5e47 X1 X2 X3
               have i₂ := b5e57 X0 X1 X2 X3
               grind)
            | exact superpose b5e57 b5e47
            | (have j0 := b5e47 X4 X1 X2
               have j1 := b5e57 X4 (M.op X0 X1) X2 X3
               grind)
            | (have r₁ := b5e47 (M.op (M.op X1 X2) (M.op X2 X3)) X1 X2
               have r₂ := b5e57 (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X1 X2) X2 X3
               grind)
            | (have r₁ := b5e47 (M.op X1 X2) X1 X2
               have r₂ := b5e57 (M.op X1 X2) (M.op X1 X2) X2 X3
               grind)
            | exact resolve b5e47 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e57
          have b5e880 : ∀ X0 X1 X4 : G, (M.op (M.op X4 X4) (M.op X4 X4)) = X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = (k (M.op X4 X4) X4) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
            intro X0 X1 X4
            first
            | (have j0 := b5e873 X0 X1 x x X4
               have j1 := b5e102 X0 X1 x x X4
               grind)
            | (have r₁ := b5e873 X0 X1 x x (k (M.op X0 X1) (M.op x x))
               have r₂ := b5e102 X0 X1 x x (M.op x x)
               grind)
            | (have r₁ := b5e873 X0 X1 x x X4
               have r₂ := b5e102 X0 X1 x x X4
               grind)
            | (have r₁ := b5e873 X0 X1 x x (M.op (M.op X0 X1) (M.op x x))
               have r₂ := b5e102 X0 X1 x x (M.op (M.op X0 X1) (M.op x x))
               grind)
            | exact resolve b5e873 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102 b5e873
          have b5e891 : ∀ X0 X1 X4 : G, (M.op (M.op X4 X4) y) = X4 ∨ (M.op (M.op X4 X4) (M.op X4 X4)) = (k (M.op X4 X4) X4) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) X4) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e880 X0 X1 X4
               have i₂ := b5e83 (M.op X4 X4) X4 X4
               grind)
            | exact superpose b5e83 b5e880
            | (have j0 := b5e880 X0 X1 X4
               grind)
            | exact resolve b5e880 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e880
          have b5e902 : ∀ X0 X1 X4 : G, (k (M.op X4 X4) X4) = (M.op (M.op X4 X4) y) ∨ (k (M.op X0 X1) X4) = (M.op (M.op X0 X1) X4) ∨ (M.op (M.op X4 X4) y) = X4 ∨ (M.op (M.op X0 X1) X4) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e891 X0 X1 X4
               have i₂ := b5e83 (M.op X4 X4) X4 X4
               grind)
            | exact superpose b5e83 b5e891
            | (have j0 := b5e891 X0 X1 X4
               grind)
            | exact resolve b5e891 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e891
          have b5e1354 : ∀ X0 X1 : G, (M.op X0 y) = (k X0 (M.op X0 y)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e124 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e124 X0 X1
               have i₂ := b5e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b5e18 b5e124
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e124 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3956 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            grind
          clear b5e667
          have b5e3989 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b5e3956 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3956
          have b5e7631 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e290 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e290
          have b5e7632 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e7631 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7631
          have b5e7633 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e7632 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7632
          have b5e7672 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e7633 X0
               have j1 := b5e270 X0
               grind)
            | (have r₁ := b5e7633 y
               have r₂ := b5e270 y
               grind)
            | (have r₁ := b5e7633 X0
               have r₂ := b5e270 X0
               grind)
            | exact resolve b5e7633 b5e270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e270 b5e7633
          have b5e7758 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e42 X0 (σ X0)
               have i₂ := b5e7672 (σ X0)
               grind)
            | exact superpose b5e7672 b5e42
            | (have j1 := b5e7672 (σ X0)
               grind)
            | exact resolve b5e42 b5e7672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e7672
          have b5e7779 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e7758 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e7758
            | (have j0 := b5e7758 X0
               grind)
            | exact resolve b5e7758 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7758
          have b5e18146 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) y) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) y) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e902 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e902
          have b5e18158 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) y) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e18146 X0
               have j1 := b5e391 (M.op X0 X0) X0
               grind)
            | (have r₁ := b5e18146 y
               have r₂ := b5e391 (M.op y y) (k (M.op y y) y)
               grind)
            | (have r₁ := b5e18146 x
               have r₂ := b5e391 (M.op x x) x
               grind)
            | (have r₁ := b5e18146 (M.op X0 y)
               have r₂ := b5e391 X0 (M.op (M.op (M.op X0 y) (M.op X0 y)) y)
               grind)
            | exact resolve b5e18146 b5e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e391 b5e18146
          have b5e18177 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e18158 X0
               have j1 := b5e112 X0 x (M.op X0 X0)
               grind)
            | (have r₁ := b5e18158 X0
               have r₂ := b5e112 X0 (M.op X0 X0) x
               grind)
            | (have r₁ := b5e18158 y
               have r₂ := b5e112 y (M.op y y) x
               grind)
            | exact resolve b5e18158 b5e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112 b5e18158
          have b5e18190 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 y) ∨ (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e18177 X0
               have i₂ := b5e121 X0
               grind)
            | exact superpose b5e121 b5e18177
            | (have j0 := b5e18177 X0
               grind)
            | exact resolve b5e18177 b5e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18177
          have b5e18199 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e18190 X0
               have i₂ := b5e121 X0
               grind)
            | exact superpose b5e121 b5e18190
            | (have j0 := b5e18190 X0
               grind)
            | exact resolve b5e18190 b5e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18190
          have b5e63160 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e17 (σ X0) (σ (M.op X0 X0))
               have i₂ := b5e3989 X0
               grind)
            | exact superpose b5e3989 b5e17
            | (have j0 := b5e17 (σ X0) (σ (M.op X0 X0))
               have j1 := b5e3989 X0
               grind)
            | (have r₁ := b5e17 (σ X0) (σ (M.op X0 X0))
               have r₂ := b5e3989 X0
               grind)
            | exact resolve b5e17 b5e3989
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3989
          have b5e63226 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b5e63160 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63160
          have b5e63227 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b5e63226 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63226
          have b5e63268 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e63227 X0
               have i₂ := b5e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e19 b5e63227
            | (have j0 := b5e63227 X0
               grind)
            | exact resolve b5e63227 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63227
          have b5e63350 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e63268
          have b5e63351 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b5e63350 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63350
          have b5e63422 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e63351 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e63351
            | exact resolve b5e63351 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63559 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e7779 X0
               have i₂ := b5e63351 X0
               grind)
            | exact superpose b5e63351 b5e7779
            | exact resolve b5e7779 b5e63351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7779
          have b5e63586 : ∀ X0 : G, (M.op (σ X0) y) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b5e18199 (σ X0)
               have i₂ := b5e63351 X0
               grind)
            | exact superpose b5e63351 b5e18199
            | (have j0 := b5e18199 (σ X0)
               grind)
            | exact resolve b5e18199 b5e63351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18199
          have b5e63696 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b5e63586 X0
               have i₂ := b5e19 (M.op X0 X0) X0
               grind)
            | exact superpose b5e19 b5e63586
            | (have j0 := b5e63586 X0
               grind)
            | exact resolve b5e63586 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63586
          have b5e63713 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e63559 X0
               have i₂ := b5e14 (M.op X0 X0)
               grind)
            | exact superpose b5e14 b5e63559
            | (have j0 := b5e63559 X0
               grind)
            | exact resolve b5e63559 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63559
          have b5e64066 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e14 (M.op (τ X0) (τ X0))
               have i₂ := b5e63422 X0
               grind)
            | exact superpose b5e63422 b5e14
            | exact resolve b5e14 b5e63422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63422
          have b5e103320 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e30 X0
               have i₂ := b5e63713 (τ X0)
               grind)
            | exact superpose b5e63713 b5e30
            | (have j1 := b5e63713 (τ X0)
               grind)
            | exact resolve b5e30 b5e63713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e103354 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 (M.op X0 X0)
               have i₂ := b5e63713 X0
               grind)
            | exact superpose b5e63713 b5e33
            | (have j1 := b5e63713 X0
               grind)
            | exact resolve b5e33 b5e63713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63713
          have b5e103589 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e103354 X0 X1
               have i₂ := b5e33 X1 X0
               grind)
            | exact superpose b5e33 b5e103354
            | (have j0 := b5e103354 X0 X1
               grind)
            | exact resolve b5e103354 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e103354
          have b5e103600 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e103320 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e103320
            | (have j0 := b5e103320 X0
               grind)
            | exact resolve b5e103320 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103320
          have b5e103694 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e103600 X0
               have i₂ := b5e63 X0 X0
               grind)
            | exact superpose b5e63 b5e103600
            | (have j0 := b5e103600 X0
               grind)
            | exact resolve b5e103600 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103600
          have b5e103750 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e103694 X0
               have i₂ := b5e64066 X0
               grind)
            | exact superpose b5e64066 b5e103694
            | (have j0 := b5e103694 X0
               grind)
            | exact resolve b5e103694 b5e64066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103694
          have b5e108317 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e15 (k X0 X0)
               have i₂ := b5e103750 X0
               grind)
            | exact superpose b5e103750 b5e15
            | (have j1 := b5e103750 X0
               grind)
            | exact resolve b5e15 b5e103750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103750
          have b5e108459 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e108317 X0
               have i₂ := b5e15 (M.op X0 X0)
               grind)
            | exact superpose b5e15 b5e108317
            | (have j0 := b5e108317 X0
               grind)
            | exact resolve b5e108317 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108317
          have b5e109422 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e108459 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108459
          have b5e110462 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) y) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e109422 (M.op X0 X1)
               have i₂ := b5e83 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b5e83 b5e109422
            | (have j0 := b5e109422 (M.op X0 X1)
               grind)
            | exact resolve b5e109422 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e109422
          have b5e408997 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            grind
          clear b5e103589
          have b5e408999 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have j0 := b5e408997 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e408997
          have b5e409002 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e408999 X0
               have i₂ := b5e63 X0 X0
               grind)
            | exact superpose b5e63 b5e408999
            | exact resolve b5e408999 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e408999
          have b5e409010 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e409002 X0
               have i₂ := b5e64066 X0
               grind)
            | exact superpose b5e64066 b5e409002
            | exact resolve b5e409002 b5e64066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64066 b5e409002
          have b5e409841 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e15 (k X0 X0)
               have i₂ := b5e409010 X0
               grind)
            | exact superpose b5e409010 b5e15
            | exact resolve b5e15 b5e409010
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e409010
          have b5e409953 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e409841 X0
               have i₂ := b5e15 (M.op X0 X0)
               grind)
            | exact superpose b5e15 b5e409841
            | exact resolve b5e409841 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e409841
          have b5e2118290 : ∀ X0 : G, y = (k x y) ∨ (M.op X0 x) = (k X0 x) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e1354 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1354
            | (have j0 := b5e1354 x X0
               grind)
            | exact resolve b5e1354 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1354
          have b5e2118301 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 x) = (k X0 x) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e2118290 X0
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e2118290
            | (have j0 := b5e2118290 X0
               grind)
            | exact resolve b5e2118290 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2118290
          have b5e2118302 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have j0 := b5e2118301 X0
               grind)
            | (have r₁ := b5e2118301 X0
               have r₂ := b5e21
               grind)
            | exact resolve b5e2118301 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2118301
          have b5e2118560 : (M.op (σ x) y) = (σ (M.op (M.op x x) x)) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op (M.op x x) x) := by
            first
            | (have i₁ := b5e63696 x
               have i₂ := b5e2118302 (M.op x x)
               grind)
            | exact superpose b5e2118302 b5e63696
            | (have j0 := b5e63696 x
               have j1 := b5e2118302 (M.op x x)
               grind)
            | exact resolve b5e63696 b5e2118302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63696 b5e2118302
          have b5e2118763 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op (M.op x x) x) := by
            first
            | (have i₁ := b5e2118560
               have i₂ := b5e121 x
               grind)
            | exact superpose b5e121 b5e2118560
            | exact resolve b5e2118560 b5e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2118560
          have b5e2118805 : (σ y) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op (M.op x x) x) := by
            first
            | (have i₁ := b5e2118763
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2118763
            | exact resolve b5e2118763 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2118763
          have b5e2118817 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b5e2118805
               have i₂ := b5e121 x
               grind)
            | exact superpose b5e121 b5e2118805
            | exact resolve b5e2118805 b5e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e121 b5e2118805
          have b5e2118822 : (σ y) = (M.op (σ x) y) ∨ x = y ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b5e2118817
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2118817
            | exact resolve b5e2118817 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2118817
          have b5e2119273 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) y) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e83 X0 (σ x) y
               have i₂ := b5e2118822
               grind)
            | exact superpose b5e2118822 b5e83
            | exact resolve b5e83 b5e2118822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e2135887 : (σ y) ≠ (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = y := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e2119273 (σ x)
               grind)
            | exact superpose b5e2119273 b5e24
            | exact resolve b5e24 b5e2119273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2119273
          have b5e2135946 : (σ x) = (M.op (σ x) y) ∨ x = y := by
            first
            | (have r₁ := b5e2135887
               have r₂ := b5e2118822
               grind)
            | exact resolve b5e2135887 b5e2118822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2118822 b5e2135887
          have b5e2136155 : (σ x) ≠ (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e110462 (σ x) y
               have i₂ := b5e2135946
               grind)
            | exact superpose b5e2135946 b5e110462
            | exact resolve b5e110462 b5e2135946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e110462
          have b5e2136189 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
            first
            | (have r₁ := b5e2136155
               have r₂ := b5e2135946
               grind)
            | exact resolve b5e2136155 b5e2135946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2135946 b5e2136155
          have b5e2136214 : (σ x) = (σ (k x x)) ∨ x = y := by
            first
            | (have i₁ := b5e2136189
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e2136189
            | exact resolve b5e2136189 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2136189
          have b5e2136227 : (σ x) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b5e2136214
               have i₂ := b5e409953 x
               grind)
            | exact superpose b5e409953 b5e2136214
            | exact resolve b5e2136214 b5e409953
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e409953 b5e2136214
          have b5e2136360 : (M.op x x) = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e14 (M.op x x)
               have i₂ := b5e2136227
               grind)
            | exact superpose b5e2136227 b5e14
            | exact resolve b5e14 b5e2136227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2136227
          have b5e2136501 : x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e2136360
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e2136360
            | exact resolve b5e2136360 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2136360
          have b5e2136855 : (M.op x y) = (k x (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b5e124 x x
               have i₂ := b5e2136501
               grind)
            | exact superpose b5e2136501 b5e124
            | exact resolve b5e124 b5e2136501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e124 b5e2136501
          have b5e2137018 : y = (k x y) ∨ x = y := by
            first
            | (have i₁ := b5e2136855
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2136855
            | exact resolve b5e2136855 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2136855
          have b5e2137127 : y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e2137018
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e2137018
            | exact resolve b5e2137018 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e2137018
          have b5e2137173 : x = y := by
            first
            | (have r₁ := b5e2137127
               have r₂ := b5e21
               grind)
            | exact resolve b5e2137127 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2137127
          have b5e2137226 : x = (M.op x x) := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e2137173
               grind)
            | exact superpose b5e2137173 b5e22
            | exact resolve b5e22 b5e2137173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2137227 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e2137173
               grind)
            | exact superpose b5e2137173 b5e24
            | exact resolve b5e24 b5e2137173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2137173
          have b5e2138391 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2137227
               have i₂ := b5e63351 x
               grind)
            | exact superpose b5e63351 b5e2137227
            | exact resolve b5e2137227 b5e63351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63351 b5e2137227
          have b5e2138490 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e2138391
               have i₂ := b5e2137226
               grind)
            | exact superpose b5e2137226 b5e2138391
            | exact resolve b5e2138391 b5e2137226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2137226 b5e2138391
          have b5e2138491 : False := by grind
          exact b5e2138491
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
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
        have b6e26 : (k x y) = (τ (σ y)) := by
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
        have b6e27 : y = (k x y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e68 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e77 : y = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e68
        have b6e83 : y = (M.op x x) := by
          first
          | (have r₁ := b6e77
             have r₂ := b6e21
             grind)
          | exact resolve b6e77 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e86 : False := by grind
        exact b6e86
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X0) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b7e29 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op X0 (σ y)) := by
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
          have b7e37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e27 X0 X1
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e38 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e39 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X2) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X0 (M.op X1 X2)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e17
            | (have j0 := b7e17 X0 (M.op X1 X2)
               grind)
            | (have r₁ := b7e17 X0 (M.op (M.op X0 X0) X0)
               have r₂ := b7e13 X0 (M.op X0 X0) X0
               grind)
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e38
          have b7e42 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 (σ y)) ∨ (M.op X1 X2) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e39 X0 X1 X2
               have i₂ := b7e29 X0
               grind)
            | exact superpose b7e29 b7e39
            | (have j0 := b7e39 X0 X1 X2
               grind)
            | (have r₁ := b7e39 (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (σ y) (σ y))
               have r₂ := b7e29 (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b7e39 X0 X0 (σ y)
               have r₂ := b7e29 X0
               grind)
            | exact resolve b7e39 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e43 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e23
               grind)
            | exact resolve b7e41 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e44 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
          have b7e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e61 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 X2
               have i₂ := b7e18 X2 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X2 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e62 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 (M.op X1 X2)) = X0 ∨ (M.op (M.op X1 X2) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X1 X2) X1 X2
               have i₂ := b7e18 (M.op X1 X2) X1
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X0 (M.op X1 X2))
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 (M.op X1 X2) X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ y)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e61 X0 X1 X2
               have i₂ := b7e29 X1
               grind)
            | exact superpose b7e29 b7e61
            | (have j0 := b7e61 X0 X1 X2
               grind)
            | exact resolve b7e61 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e67 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e29 X0
               grind)
            | exact superpose b7e29 b7e13
            | exact resolve b7e13 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e23
            | exact resolve b7e23 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e72 : (M.op (σ x) (σ y)) = (M.op (σ (k x y)) (σ x)) := by
            first
            | (have i₁ := b7e29 (σ x)
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e29
            | exact resolve b7e29 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e75 : (σ (k x y)) = (k (σ x) (σ (k x y))) := by grind
          have b7e79 : (σ (k x y)) = (σ (k x (k x y))) := by
            first
            | (have i₁ := b7e75
               have i₂ := b7e19 x (k x y)
               grind)
            | exact superpose b7e19 b7e75
            | exact resolve b7e75 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e81 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e72
            | exact resolve b7e72 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e281 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ y) = (M.op (σ x) X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e24
               have i₂ := b7e64 X0 (σ x) X1
               grind)
            | (have i₁ := b7e24
               have i₂ := b7e64 (σ y) (σ x) x
               grind)
            | exact superpose b7e64 b7e24
            | (have j1 := b7e64 X0 X1 X1
               grind)
            | exact resolve b7e24 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e300 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e81
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e81
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e81 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e306 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e300
               have r₂ := b7e21
               grind)
            | exact resolve b7e300 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e300
          have b7e309 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
            first
            | (have r₁ := b7e306
               have r₂ := b7e22
               grind)
            | exact resolve b7e306 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e306
          have b7e491 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (σ y))) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b7e42 X0 X0 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e581 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e56 x x
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e56
            | exact resolve b7e56 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e651 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e662 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by grind
          clear b7e581
          have b7e710 : (k x (k x y)) = (τ (σ (k x y))) := by
            first
            | (have i₁ := b7e14 (k x (k x y))
               have i₂ := b7e79
               grind)
            | exact superpose b7e79 b7e14
            | exact resolve b7e14 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e727 : (k x y) = (k x (k x y)) := by
            first
            | (have i₁ := b7e710
               have i₂ := b7e14 (k x y)
               grind)
            | exact superpose b7e14 b7e710
            | exact resolve b7e710 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e710
          have b7e782 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e727
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e727
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e727 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e727
          have b7e807 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e782
               have r₂ := b7e21
               grind)
            | exact resolve b7e782 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e782
          have b7e811 : (M.op x y) = (k x (M.op x y)) := by
            first
            | (have r₁ := b7e807
               have r₂ := b7e22
               grind)
            | exact resolve b7e807 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e807
          have b7e870 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b7e18 x (M.op x y)
               have i₂ := b7e811
               grind)
            | exact superpose b7e811 b7e18
            | (have j0 := b7e18 x (M.op x y)
               grind)
            | exact resolve b7e18 b7e811
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e871 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e870
          have b7e882 : (M.op x y) = (M.op x (σ y)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e871
               have i₂ := b7e67 x x y
               grind)
            | exact superpose b7e67 b7e871
            | exact resolve b7e871 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e871
          have b7e1379 : (k x y) = (τ (σ (k x x))) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e662
               grind)
            | exact superpose b7e662 b7e14
            | exact resolve b7e14 b7e662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e662
          have b7e1408 : (σ x) = (σ (k x y)) ∨ (k x y) = (k x x) := by
            first
            | (have i₁ := b7e1379
               have i₂ := b7e14 (k x x)
               grind)
            | exact superpose b7e14 b7e1379
            | exact resolve b7e1379 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1379
          have b7e1480 : (σ y) = (M.op (σ x) (σ x)) ∨ (k x y) = (k x x) := by
            first
            | (have i₁ := b7e81
               have i₂ := b7e1408
               grind)
            | exact superpose b7e1408 b7e81
            | exact resolve b7e81 b7e1408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e1408
          have b7e1513 : (k x y) = (k x x) := by
            first
            | (have r₁ := b7e1480
               have r₂ := b7e23
               grind)
            | exact resolve b7e1480 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1480
          have b7e1537 : (σ y) ≠ (σ (k x x)) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e1513
               grind)
            | exact superpose b7e1513 b7e71
            | exact resolve b7e71 b7e1513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e1513
          have b7e1656 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e281 (σ x) X0
               grind)
            | exact superpose b7e281 b7e23
            | (have j1 := b7e281 (σ x) X0
               grind)
            | (have r₁ := b7e23
               have r₂ := b7e281 (σ x) x
               grind)
            | exact resolve b7e23 b7e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e281
          have b7e1686 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b7e1656 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1656
          have b7e3470 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            grind
          clear b7e651
          have b7e3513 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b7e3470 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3470
          have b7e8363 : (M.op x x) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e491 x
               have i₂ := b7e882
               grind)
            | exact superpose b7e882 b7e491
            | exact resolve b7e491 b7e882
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e491 b7e882
          have b7e8378 : (M.op x x) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e8363
          have b7e8380 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e8378
               have i₂ := b7e811
               grind)
            | exact superpose b7e811 b7e8378
            | exact resolve b7e8378 b7e811
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e811 b7e8378
          have b7e8381 : (M.op x y) = (M.op x x) := by grind
          clear b7e8380
          have b7e8505 : (σ y) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b7e309
               have i₂ := b7e8381
               grind)
            | exact superpose b7e8381 b7e309
            | exact resolve b7e309 b7e8381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e309 b7e8381
          have b7e12958 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e37 X0 x
               have i₂ := b7e1686 X0
               grind)
            | exact superpose b7e1686 b7e37
            | (have j1 := b7e1686 X0
               grind)
            | exact resolve b7e37 b7e1686
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e12972 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 x
               have i₂ := b7e1686 (σ X0)
               grind)
            | exact superpose b7e1686 b7e19
            | (have j1 := b7e1686 (σ X0)
               grind)
            | exact resolve b7e19 b7e1686
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1686
          have b7e34086 : (τ (σ y)) = (k (τ (σ (M.op x x))) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e12958 (σ (M.op x x))
               have i₂ := b7e8505
               grind)
            | exact superpose b7e8505 b7e12958
            | exact resolve b7e12958 b7e8505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12958
          have b7e34153 : (τ (σ y)) = (k (M.op x x) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e34086
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e34086
            | exact resolve b7e34086 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34086
          have b7e34180 : y = (k (M.op x x) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e34153
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e34153
            | exact resolve b7e34153 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34153
          have b7e34494 : y = (M.op (M.op x x) x) ∨ x = (M.op x (M.op x x)) ∨ x = (M.op (M.op x x) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e62 x x x
               have i₂ := b7e34180
               grind)
            | exact superpose b7e34180 b7e62
            | (have j0 := b7e62 x x x
               grind)
            | exact resolve b7e62 b7e34180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62 b7e34180
          have b7e34527 : y = (M.op x (σ y)) ∨ x = (M.op x (M.op x x)) ∨ x = (M.op (M.op x x) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e34494
               have i₂ := b7e29 x
               grind)
            | exact superpose b7e29 b7e34494
            | exact resolve b7e34494 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34494
          have b7e34552 : x = (M.op x (σ y)) ∨ y = (M.op x (σ y)) ∨ x = (M.op (M.op x x) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e34527
               have i₂ := b7e67 x x x
               grind)
            | exact superpose b7e67 b7e34527
            | exact resolve b7e34527 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34527
          have b7e34567 : x = (M.op x (σ y)) ∨ x = (M.op x (σ y)) ∨ y = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e34552
               have i₂ := b7e29 x
               grind)
            | exact superpose b7e29 b7e34552
            | exact resolve b7e34552 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e34552
          have b7e34568 : y = (M.op x (σ y)) ∨ x = (M.op x (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b7e34567
          have b7e39847 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) ∨ x = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e67 X0 x (σ y)
               have i₂ := b7e34568
               grind)
            | exact superpose b7e34568 b7e67
            | exact resolve b7e67 b7e34568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39867 : x ≠ y ∨ x = (M.op x (σ y)) ∨ (σ x) = (σ y) := by grind
          have b7e64602 : (σ y) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e12972 (M.op x x)
               have i₂ := b7e8505
               grind)
            | exact superpose b7e8505 b7e12972
            | exact resolve b7e12972 b7e8505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8505 b7e12972
          have b7e102686 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e17 (σ X0) (σ (M.op X0 X0))
               have i₂ := b7e3513 X0
               grind)
            | exact superpose b7e3513 b7e17
            | (have j0 := b7e17 (σ X0) (σ (M.op X0 X0))
               have j1 := b7e3513 X0
               grind)
            | (have r₁ := b7e17 (σ X0) (σ (M.op X0 X0))
               have r₂ := b7e3513 X0
               grind)
            | exact resolve b7e17 b7e3513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3513
          have b7e102731 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b7e102686 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102686
          have b7e102732 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b7e102731 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102731
          have b7e102769 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e102732 X0
               have i₂ := b7e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e19 b7e102732
            | (have j0 := b7e102732 X0
               grind)
            | exact resolve b7e102732 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102732
          have b7e102893 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e102769
          have b7e102894 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b7e102893 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102893
          have b7e659664 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e39847 x
               have i₂ := b7e34568
               grind)
            | exact superpose b7e34568 b7e39847
            | exact resolve b7e39847 b7e34568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34568 b7e39847
          have b7e660009 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x (σ y)) := by grind
          clear b7e659664
          have b7e660044 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (σ y)) := by
            first
            | (have r₁ := b7e660009
               have r₂ := b7e39867
               grind)
            | exact resolve b7e660009 b7e39867
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39867 b7e660009
          have b7e660073 : x = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e660044
               have r₂ := b7e22
               grind)
            | exact resolve b7e660044 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e660044
          have b7e661967 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e67 X0 x (σ y)
               have i₂ := b7e660073
               grind)
            | exact superpose b7e660073 b7e67
            | exact resolve b7e67 b7e660073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e666824 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e660073
               have i₂ := b7e661967 x
               grind)
            | exact superpose b7e661967 b7e660073
            | exact resolve b7e660073 b7e661967
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e660073 b7e661967
          have b7e666829 : x = (M.op x x) ∨ (σ x) = (σ y) := by grind
          clear b7e666824
          have b7e667036 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e64602
               have i₂ := b7e666829
               grind)
            | exact superpose b7e666829 b7e64602
            | exact resolve b7e64602 b7e666829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64602 b7e666829
          have b7e667214 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e667036
          have b7e667268 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e667214
               have r₂ := b7e1537
               grind)
            | exact resolve b7e667214 b7e1537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1537 b7e667214
          have b7e667292 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e667268
               grind)
            | exact superpose b7e667268 b7e24
            | exact resolve b7e24 b7e667268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e667583 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e667268
               grind)
            | exact superpose b7e667268 b7e14
            | exact resolve b7e14 b7e667268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e667268
          have b7e667854 : x = y := by
            first
            | (have i₁ := b7e667583
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e667583
            | exact resolve b7e667583 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e667583
          have b7e667909 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e667292
               have i₂ := b7e102894 x
               grind)
            | exact superpose b7e102894 b7e667292
            | exact resolve b7e667292 b7e102894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102894 b7e667292
          have b7e668099 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e667854
               grind)
            | exact superpose b7e667854 b7e26
            | exact resolve b7e26 b7e667854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e667854
          have b7e668623 : False := by grind
          exact b7e668623
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e139 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e140 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e139
               have r₂ := b8e24
               grind)
            | exact resolve b8e139 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e141 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e140
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e140
            | exact resolve b8e140 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e142 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e141
               grind)
            | exact superpose b8e141 b8e20
            | exact resolve b8e20 b8e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e141
          have b8e287 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e142
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e142
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e142 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e142
          have b8e288 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e287
          have b8e290 : y = (M.op x y) := by
            first
            | (have r₁ := b8e288
               have r₂ := b8e21
               grind)
            | exact resolve b8e288 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e288
          have b8e292 : False := by grind
          exact b8e292
