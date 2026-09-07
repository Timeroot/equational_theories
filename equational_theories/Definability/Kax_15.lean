import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_x_pxy_Equation3744 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e31 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 y X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b0e11 (M.op X0 X2) X3 (M.op x X1) X5
           have i₂ := b0e11 X0 X1 X2 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e33 X0 x X2 X3 x
           have i₂ := b0e11 X0 X3 x x
           grind)
        | exact superpose b0e11 b0e33
        | exact resolve b0e33 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e45 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e11 x X1 (M.op x X0) X3
           have i₂ := b0e31 X0 x
           grind)
        | exact superpose b0e31 b0e11
        | exact resolve b0e11 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e46 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
        intro X1
        first
        | (have i₁ := b0e45 x X1 x
           have i₂ := b0e11 y X1 x x
           grind)
        | exact superpose b0e11 b0e45
        | exact resolve b0e45 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e188 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e39 (σ y) (σ y) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e39
        | exact resolve b0e39 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e407 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e188 (σ y)
           grind)
        | exact superpose b0e188 b0e18
        | exact resolve b0e18 b0e188
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e188
      have b0e433 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e407
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e407
        | exact resolve b0e407 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e407
      have b0e441 : (σ x) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e433
           have i₂ := b0e46 y
           grind)
        | exact superpose b0e46 b0e433
        | exact resolve b0e433 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e433
      have b0e446 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e441
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e441
        | exact resolve b0e441 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e441
      have b0e447 : False := by grind
      exact b0e447
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y = (k x y) := by grind
        have b1e27 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X0 y X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e12 x X1 (M.op x X0) X3
             have i₂ := b1e27 X0 x
             grind)
          | exact superpose b1e27 b1e12
          | exact resolve b1e12 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e42 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b1e41 x X1 x
             have i₂ := b1e12 y X1 x x
             grind)
          | exact superpose b1e12 b1e41
          | exact resolve b1e41 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e47 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e50 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e47
        have b1e52 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e50
             have r₂ := b1e21
             grind)
          | exact resolve b1e50 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e54 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e55 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e54
          | exact resolve b1e54 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e54
        have b1e56 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e19
          | exact resolve b1e19 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e22
          | exact resolve b1e22 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e56
          | exact resolve b1e56 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e57
        have b1e65 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e64
             have i₂ := b1e42 y
             grind)
          | exact superpose b1e42 b1e64
          | exact resolve b1e64 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e64
        have b1e66 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e65
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e65
          | exact resolve b1e65 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e67 : False := by grind
        exact b1e67
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e27 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X0 y X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b2e38 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e12 x X1 (M.op x X0) X3
             have i₂ := b2e27 X0 x
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e39 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b2e38 x X1 x
             have i₂ := b2e12 y X1 x x
             grind)
          | exact superpose b2e12 b2e38
          | exact resolve b2e38 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e64 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
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
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e600 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e64 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e601 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e600
             have r₂ := b2e22
             grind)
          | exact resolve b2e600 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e600
        have b2e602 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e601
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e601
          | exact resolve b2e601 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e601
        have b2e603 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e602
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e602
          | exact resolve b2e602 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e602
        have b2e608 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e603
             grind)
          | exact superpose b2e603 b2e19
          | exact resolve b2e19 b2e603
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e614 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b2e31 (σ x) (σ y)
             have i₂ := b2e603
             grind)
          | exact superpose b2e603 b2e31
          | exact resolve b2e31 b2e603
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e603
        have b2e620 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b2e614
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e614
          | exact resolve b2e614 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e614
        have b2e624 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e608
             have i₂ := b2e39 y
             grind)
          | exact superpose b2e39 b2e608
          | exact resolve b2e608 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e608
        have b2e626 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e624
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e624
          | exact resolve b2e624 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e624
        have b2e744 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e620
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e620
          | (have j1 := b2e17 y y
             grind)
          | exact resolve b2e620 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e620
        have b2e751 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b2e744
        have b2e757 : (σ x) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e751
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e751
          | exact resolve b2e751 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e751
        have b2e759 : y = (M.op y y) := by
          first
          | (have r₁ := b2e757
             have r₂ := b2e626
             grind)
          | exact resolve b2e757 b2e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e757
        have b2e1031 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e759
             grind)
          | exact superpose b2e759 b2e20
          | exact resolve b2e20 b2e759
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e759
        have b2e1103 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e626
             have i₂ := b2e1031
             grind)
          | exact superpose b2e1031 b2e626
          | exact resolve b2e626 b2e1031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e626 b2e1031
        have b2e1104 : False := by grind
        exact b2e1104
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e25 : (σ y) = (σ (k x y)) := by
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
        have b3e26 : (k x y) = (τ (σ y)) := by
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
        have b3e27 : y = (k x y) := by
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
        have b3e38 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
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
        have b3e47 : y = (M.op y y) := by
          first
          | (have i₁ := b3e38 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e38
          | exact resolve b3e38 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e55 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) := by
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
        have b3e59 : x = (M.op y y) ∨ x = (k x y) := by grind
        clear b3e55
        have b3e62 : x = (k x y) := by
          first
          | (have r₁ := b3e59
             have r₂ := b3e20
             grind)
          | exact resolve b3e59 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e63 : x = y := by
          first
          | (have i₁ := b3e62
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e62
          | exact resolve b3e62 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e62
        have b3e64 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e63
             grind)
          | exact superpose b3e63 b3e19
          | exact resolve b3e19 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e68 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e64
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e64
          | exact resolve b3e64 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e64
        have b3e69 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e68
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e68
          | exact resolve b3e68 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e70 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e69
             have i₂ := b3e63
             grind)
          | exact superpose b3e63 b3e69
          | exact resolve b3e69 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63 b3e69
        have b3e71 : False := by grind
        exact b3e71
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
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e30 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
          have b4e36 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e30 X0 x X2 X3 x
               have i₂ := b4e13 X0 X3 x x
               grind)
            | exact superpose b4e13 b4e30
            | exact resolve b4e30 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b4e65 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X1 X3) X0) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X3 X2
               have i₂ := b4e18 X0 X2
               grind)
            | (have i₁ := b4e13 X0 X1 X2 X3
               have i₂ := b4e18 (M.op X3 X1) X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 X2
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e65 X0 X1 X2 x
               have i₂ := b4e36 X1 x X0
               grind)
            | exact superpose b4e36 b4e65
            | (have j0 := b4e65 X0 X1 X2 x
               grind)
            | exact resolve b4e65 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65
          have b4e89 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
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
          have b4e92 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b4e89 x X1 x
               have i₂ := b4e13 X1 x x x
               grind)
            | exact superpose b4e13 b4e89
            | exact resolve b4e89 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89
          have b4e103 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
          have b4e171 : x = (k (M.op x y) x) := by grind
          have b4e624 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e71 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e985 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e18 X1 (σ X0)
               have i₂ := b4e60 X0 X0
               grind)
            | exact superpose b4e60 b4e18
            | (have j0 := b4e18 X1 (σ X0)
               have j1 := b4e60 X0 X0
               grind)
            | exact resolve b4e18 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e994 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ (k X0 X1)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (σ X0) (σ X1)
               have i₂ := b4e60 X0 X1
               grind)
            | exact superpose b4e60 b4e34
            | (have j1 := b4e60 X0 X1
               grind)
            | exact resolve b4e34 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1055 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e60 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e1056 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e1055 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1055
          have b4e1061 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e985 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e985
          have b4e1085 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 X1) (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e994 X0 X1
               have i₂ := b4e19 (k X0 X1) (k X0 X1)
               grind)
            | exact superpose b4e19 b4e994
            | (have j0 := b4e994 X0 X1
               grind)
            | exact resolve b4e994 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e994
          have b4e1092 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ (k X0 X0)) = X1 ∨ (σ X0) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e1061 X0 X1
               have j1 := b4e624 (σ X0) X1
               grind)
            | (have r₁ := b4e1061 X0 (M.op (σ (k X0 X0)) (σ (k X0 X0)))
               have r₂ := b4e624 (σ (k X0 X0)) X1
               grind)
            | (have r₁ := b4e1061 X0 (σ X0)
               have r₂ := b4e624 (σ X0) X1
               grind)
            | (have r₁ := b4e1061 X0 X1
               have r₂ := b4e624 (σ X0) X1
               grind)
            | exact resolve b4e1061 b4e624
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e624 b4e1061
          have b4e4699 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e1092 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1092
            | (have j0 := b4e1092 (τ X0) X1
               grind)
            | exact resolve b4e1092 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1092
          have b4e4847 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e4699 X0 X1
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e4699
            | (have j0 := b4e4699 X0 X1
               grind)
            | exact resolve b4e4699 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e4699
          have b4e4872 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e4847 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e4847
            | (have j0 := b4e4847 X0 X1
               grind)
            | exact resolve b4e4847 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4847
          have b4e24177 : (σ x) = (σ (k x x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e1085 (M.op x y) x
               have i₂ := b4e171
               grind)
            | exact superpose b4e171 b4e1085
            | (have j0 := b4e1085 (M.op x y) x
               grind)
            | exact resolve b4e1085 b4e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1085
          have b4e24358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e24177
               have i₂ := b4e103 (σ x)
               grind)
            | exact superpose b4e103 b4e24177
            | exact resolve b4e24177 b4e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24177
          have b4e24376 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have r₁ := b4e24358
               have r₂ := b4e20
               grind)
            | exact resolve b4e24358 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24358
          have b4e31345 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (k x x) ∨ x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e171
               have i₂ := b4e4872 x (M.op x y)
               grind)
            | exact superpose b4e4872 b4e171
            | (have j1 := b4e4872 x (M.op x y)
               grind)
            | exact resolve b4e171 b4e4872
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e171 b4e4872
          have b4e31502 : x = (M.op x x) ∨ (M.op x y) = (k x x) ∨ x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e31345
               have i₂ := b4e36 x y x
               grind)
            | exact superpose b4e36 b4e31345
            | exact resolve b4e31345 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e31345
          have b4e31536 : x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e31502
               have i₂ := b4e92 x
               grind)
            | exact superpose b4e92 b4e31502
            | exact resolve b4e31502 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92 b4e31502
          have b4e31547 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) := by
            first
            | (have i₁ := b4e31536
               have i₂ := b4e35 y x x
               grind)
            | exact superpose b4e35 b4e31536
            | exact resolve b4e31536 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e31536
          have b4e31548 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
          clear b4e31547
          have b4e48497 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e34 (σ x) (σ (M.op x y))
               have i₂ := b4e24376
               grind)
            | exact superpose b4e24376 b4e34
            | exact resolve b4e34 b4e24376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e24376
          have b4e48542 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e48497
               have i₂ := b4e19 x x
               grind)
            | exact superpose b4e19 b4e48497
            | exact resolve b4e48497 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48497
          have b4e48543 : (σ x) = (σ (k x x)) := by grind
          clear b4e48542
          have b4e48826 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e1056 x
               have i₂ := b4e48543
               grind)
            | exact superpose b4e48543 b4e1056
            | (have j0 := b4e1056 x
               grind)
            | (have r₁ := b4e1056 x
               have r₂ := b4e48543
               grind)
            | exact resolve b4e1056 b4e48543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1056
          have b4e48827 : (τ (σ x)) = (k x x) := by
            first
            | (have i₁ := b4e14 (k x x)
               have i₂ := b4e48543
               grind)
            | exact superpose b4e48543 b4e14
            | exact resolve b4e14 b4e48543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48543
          have b4e48916 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e48826
          have b4e49000 : x = (k x x) := by
            first
            | (have i₁ := b4e48827
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e48827
            | exact resolve b4e48827 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48827
          have b4e49001 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e48916
               have i₂ := b4e103 (σ x)
               grind)
            | exact superpose b4e103 b4e48916
            | exact resolve b4e48916 b4e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103 b4e48916
          have b4e49387 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e31548
               have i₂ := b4e49000
               grind)
            | exact superpose b4e49000 b4e31548
            | exact resolve b4e31548 b4e49000
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31548 b4e49000
          have b4e49471 : x = (M.op x y) := by grind
          clear b4e49387
          have b4e54292 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e49001
               grind)
            | exact superpose b4e49001 b4e20
            | exact resolve b4e20 b4e49001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49001
          have b4e54436 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e54292
               have i₂ := b4e49471
               grind)
            | exact superpose b4e49471 b4e54292
            | exact resolve b4e54292 b4e49471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49471 b4e54292
          have b4e54437 : False := by grind
          exact b4e54437
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b5e32 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b5e42 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) := by
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
          have b5e45 : x = (M.op y y) ∨ x = (k x y) := by grind
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
          have b5e61 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
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
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
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
          clear b5e30
          have b5e84 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b5e81 x X1 x
               have i₂ := b5e13 X1 x x x
               grind)
            | exact superpose b5e13 b5e81
            | exact resolve b5e81 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e540 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e61 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e541 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e540
               have r₂ := b5e24
               grind)
            | exact resolve b5e540 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e540
          have b5e542 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e541
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e541
            | exact resolve b5e541 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e541
          have b5e543 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e542
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e542
            | exact resolve b5e542 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e542
          have b5e548 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e543
               grind)
            | exact superpose b5e543 b5e20
            | exact resolve b5e20 b5e543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e554 : (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b5e32 (σ x) (σ y)
               have i₂ := b5e543
               grind)
            | exact superpose b5e543 b5e32
            | exact resolve b5e32 b5e543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e543
          have b5e561 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b5e554
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e554
            | exact resolve b5e554 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e554
          have b5e660 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e561
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e561
            | (have j1 := b5e18 x x
               grind)
            | exact resolve b5e561 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e561
          have b5e667 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b5e660
          have b5e674 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e667
               have i₂ := b5e84 x
               grind)
            | exact superpose b5e84 b5e667
            | exact resolve b5e667 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e667
          have b5e677 : x = (M.op x x) := by
            first
            | (have r₁ := b5e674
               have r₂ := b5e548
               grind)
            | exact resolve b5e674 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e674
          have b5e679 : x = (M.op x y) := by
            first
            | (have i₁ := b5e677
               have i₂ := b5e84 x
               grind)
            | exact superpose b5e84 b5e677
            | exact resolve b5e677 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84 b5e677
          have b5e990 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e548
               have i₂ := b5e679
               grind)
            | exact superpose b5e679 b5e548
            | exact resolve b5e548 b5e679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e548 b5e679
          have b5e1003 : False := by grind
          exact b5e1003
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
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
        have b6e39 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
        have b6e44 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b6e39 X0 x X2 X3 x
             have i₂ := b6e12 X0 X3 x x
             grind)
          | exact superpose b6e12 b6e39
          | exact resolve b6e39 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e90 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
        have b6e108 : y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e90
             have r₂ := b6e20
             grind)
          | exact resolve b6e90 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e117 : y = (M.op x y) := by
          first
          | (have r₁ := b6e108
             have r₂ := b6e21
             grind)
          | exact resolve b6e108 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108
        have b6e126 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e44 x y X0
             have i₂ := b6e117
             grind)
          | exact superpose b6e117 b6e44
          | exact resolve b6e44 b6e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e178 : y = (M.op y y) := by
          first
          | (have i₁ := b6e117
             have i₂ := b6e126 y
             grind)
          | exact superpose b6e126 b6e117
          | exact resolve b6e117 b6e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e117 b6e126
        have b6e224 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e178
             grind)
          | exact superpose b6e178 b6e20
          | exact resolve b6e20 b6e178
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e225 : y = (k y y) := by grind
        clear b6e178
        have b6e427 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e88 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e88
          | exact resolve b6e88 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e487 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
        clear b6e427
        have b6e513 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e487
             have i₂ := b6e225
             grind)
          | exact superpose b6e225 b6e487
          | exact resolve b6e487 b6e225
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e225 b6e487
        have b6e514 : (σ x) = (σ y) := by grind
        clear b6e513
        have b6e593 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e514
             grind)
          | exact superpose b6e514 b6e13
          | exact resolve b6e13 b6e514
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e514
        have b6e606 : x = y := by
          first
          | (have i₁ := b6e593
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e593
          | exact resolve b6e593 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e593
        have b6e611 : False := by grind
        exact b6e611
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b7e47 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e47
          have b7e52 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
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
          have b7e89 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
          have b7e90 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e89
               have r₂ := b7e21
               grind)
            | exact resolve b7e89 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e92 : x = (M.op x y) := by
            first
            | (have r₁ := b7e90
               have r₂ := b7e22
               grind)
            | exact resolve b7e90 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e123 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e33 y X0 x
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e33
            | exact resolve b7e33 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e92
          have b7e160 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e123 y
               grind)
            | exact superpose b7e123 b7e22
            | exact resolve b7e22 b7e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e123
          have b7e224 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e32 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e231 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e224
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e224
            | exact resolve b7e224 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e224
          have b7e235 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e231
               grind)
            | exact superpose b7e231 b7e14
            | exact resolve b7e14 b7e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e231
          have b7e237 : y = (k y y) := by
            first
            | (have i₁ := b7e235
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e235
            | exact resolve b7e235 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e235
          have b7e258 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e237
               grind)
            | exact superpose b7e237 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e237
          have b7e259 : y = (M.op y y) := by grind
          clear b7e258
          have b7e262 : False := by grind
          exact b7e262
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e81 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
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
          have b8e181 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e81 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e182 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e181
               have r₂ := b8e24
               grind)
            | exact resolve b8e181 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181
          have b8e183 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e182
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e182
            | exact resolve b8e182 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182
          have b8e184 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e183
               grind)
            | exact superpose b8e183 b8e20
            | exact resolve b8e20 b8e183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e183
          have b8e215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e184
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e184
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e184 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e216 : x = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e215
          have b8e218 : y = (M.op y x) := by
            first
            | (have r₁ := b8e216
               have r₂ := b8e21
               grind)
            | exact resolve b8e216 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e216
          have b8e220 : False := by grind
          exact b8e220

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pxy_Equation3756 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3756 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e28 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op x (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op X0 X0) x X1
           have i₂ := b0e28 X0
           grind)
        | exact superpose b0e28 b0e11
        | exact resolve b0e11 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) := by
        intro X0
        first
        | (have i₁ := b0e38 X0 x
           have i₂ := b0e28 x
           grind)
        | exact superpose b0e28 b0e38
        | exact resolve b0e38 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e38
      have b0e40 : ∀ X0 : G, (M.op X0 X0) = x := by
        intro X0
        first
        | (have i₁ := b0e39 X0
           have i₂ := b0e31 X0 X0
           grind)
        | exact superpose b0e31 b0e39
        | exact resolve b0e39 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e41 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
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
      have b0e46 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e41 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e55 : x = (σ x) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e40 (σ x)
           grind)
        | exact superpose b0e40 b0e20
        | exact resolve b0e20 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e62 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e55
           grind)
        | exact superpose b0e55 b0e18
        | exact resolve b0e18 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e65 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e55
           grind)
        | exact superpose b0e55 b0e17
        | exact resolve b0e17 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e67 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) := by
        intro X0
        first
        | (have i₁ := b0e65 X0
           have i₂ := b0e46 (σ X0)
           grind)
        | exact superpose b0e46 b0e65
        | exact resolve b0e65 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e68 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e67 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e67
        | exact resolve b0e67 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e67
      have b0e386 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X0)) x) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e68 (M.op X1 X0)
           have i₂ := b0e31 X0 X1
           grind)
        | exact superpose b0e31 b0e68
        | exact resolve b0e68 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1636 : ∀ X0 : G, (M.op (M.op (σ X0) x) x) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e386 x X0
           have i₂ := b0e68 X0
           grind)
        | exact superpose b0e68 b0e386
        | exact resolve b0e386 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68 b0e386
      have b0e1656 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e1636 X0
           have i₂ := b0e31 x (σ X0)
           grind)
        | exact superpose b0e31 b0e1636
        | exact resolve b0e1636 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e1636
      have b0e1742 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e62
           have i₂ := b0e1656 y
           grind)
        | exact superpose b0e1656 b0e62
        | (have r₁ := b0e62
           have r₂ := b0e1656 y
           grind)
        | exact resolve b0e62 b0e1656
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62 b0e1656
      have b0e1762 : False := by grind
      exact b0e1762
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op x (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op X0 X0) x X1
             have i₂ := b1e27 X0
             grind)
          | exact superpose b1e27 b1e12
          | exact resolve b1e12 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b1e37 X0 x
             have i₂ := b1e27 x
             grind)
          | exact superpose b1e27 b1e37
          | exact resolve b1e37 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e37
        have b1e39 : ∀ X0 : G, (M.op X0 X0) = x := by
          intro X0
          first
          | (have i₁ := b1e38 X0
             have i₂ := b1e30 X0 X0
             grind)
          | exact superpose b1e30 b1e38
          | exact resolve b1e38 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e38
        have b1e49 : ∀ X0 X1 : G, x ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X0 X1
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e15
          | (have j0 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e15 x X1
             have r₂ := b1e39 x
             grind)
          | exact resolve b1e15 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : x = (σ y) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e39 (σ x)
             grind)
          | exact superpose b1e39 b1e22
          | exact resolve b1e22 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : x ≠ (σ x) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e24
          | exact resolve b1e24 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e53
        have b1e88 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e17 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e90 : ∀ X0 X1 : G, X0 ≠ X1 ∨ x = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e88 X0 X1
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e88
          | (have j0 := b1e88 X0 X1
             grind)
          | (have r₁ := b1e88 (M.op X0 X0) x
             have r₂ := b1e39 X0
             grind)
          | (have r₁ := b1e88 x (M.op X0 X0)
             have r₂ := b1e39 X0
             grind)
          | exact resolve b1e88 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88
        have b1e356 : ∀ X0 : G, x = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e90 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e357 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e356 X0
             have j1 := b1e49 X0 X0
             grind)
          | (have r₁ := b1e356 X0
             have r₂ := b1e49 X0 x
             grind)
          | (have r₁ := b1e356 x
             have r₂ := b1e49 x x
             grind)
          | exact resolve b1e356 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e356
        have b1e358 : ∀ X0 : G, x = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e357 X0
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e357
          | exact resolve b1e357 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e357
        have b1e365 : ∀ X0 : G, x = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e358 (σ X0)
             grind)
          | exact superpose b1e358 b1e18
          | exact resolve b1e18 b1e358
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e372 : x = (σ x) := by
          first
          | (have i₁ := b1e365 x
             have i₂ := b1e358 x
             grind)
          | exact superpose b1e358 b1e365
          | exact resolve b1e365 b1e358
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e358 b1e365
        have b1e376 : False := by grind
        exact b1e376
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e26 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 x x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op x (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op X0 X0) x X1
             have i₂ := b2e26 X0
             grind)
          | exact superpose b2e26 b2e12
          | exact resolve b2e12 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b2e33 X0 x
             have i₂ := b2e26 x
             grind)
          | exact superpose b2e26 b2e33
          | exact resolve b2e33 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e33
        have b2e35 : ∀ X0 : G, (M.op X0 X0) = x := by
          intro X0
          first
          | (have i₁ := b2e34 X0
             have i₂ := b2e28 X0 X0
             grind)
          | exact superpose b2e28 b2e34
          | exact resolve b2e34 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e34
        have b2e43 : ∀ X0 X1 : G, x ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e35 X0
             grind)
          | exact superpose b2e35 b2e15
          | (have j0 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e15 x X1
             have r₂ := b2e35 x
             grind)
          | exact resolve b2e15 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : x ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e35 (σ x)
             grind)
          | exact superpose b2e35 b2e21
          | exact resolve b2e21 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e17 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 X1 : G, X0 ≠ X1 ∨ x = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e73 X0 X1
             have i₂ := b2e35 X0
             grind)
          | exact superpose b2e35 b2e73
          | (have j0 := b2e73 X0 X1
             grind)
          | (have r₁ := b2e73 (M.op X0 X0) x
             have r₂ := b2e35 X0
             grind)
          | (have r₁ := b2e73 x (M.op X0 X0)
             have r₂ := b2e35 X0
             grind)
          | exact resolve b2e73 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e239 : ∀ X0 : G, x = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e76 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e240 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e239 X0
             have j1 := b2e43 X0 X0
             grind)
          | (have r₁ := b2e239 X0
             have r₂ := b2e43 X0 x
             grind)
          | (have r₁ := b2e239 x
             have r₂ := b2e43 x x
             grind)
          | exact resolve b2e239 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43 b2e239
        have b2e241 : ∀ X0 : G, x = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e240 X0
             have i₂ := b2e35 X0
             grind)
          | exact superpose b2e35 b2e240
          | exact resolve b2e240 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e240
        have b2e249 : ∀ X0 : G, x = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e241 (σ X0)
             grind)
          | exact superpose b2e241 b2e18
          | exact resolve b2e18 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e256 : x = (σ x) := by
          first
          | (have i₁ := b2e249 x
             have i₂ := b2e241 x
             grind)
          | exact superpose b2e241 b2e249
          | exact resolve b2e249 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e241 b2e249
        have b2e261 : False := by grind
        exact b2e261
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
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
        have b3e30 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op y (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op X0 X0) y X1
             have i₂ := b3e27 X0
             grind)
          | exact superpose b3e27 b3e12
          | exact resolve b3e12 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
          intro X0
          first
          | (have i₁ := b3e37 X0 x
             have i₂ := b3e27 x
             grind)
          | exact superpose b3e27 b3e37
          | exact resolve b3e37 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e37
        have b3e39 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b3e38 X0
             have i₂ := b3e30 X0 X0
             grind)
          | exact superpose b3e30 b3e38
          | exact resolve b3e38 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e38
        have b3e71 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e17 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ y = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e71 X0 X1
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e71
          | (have j0 := b3e71 X0 X1
             grind)
          | (have r₁ := b3e71 (M.op X0 X0) y
             have r₂ := b3e39 X0
             grind)
          | (have r₁ := b3e71 y (M.op X0 X0)
             have r₂ := b3e39 X0
             grind)
          | exact resolve b3e71 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e101 : ∀ X0 X1 : G, y ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e15
          | (have j0 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e15 y X1
             have r₂ := b3e39 y
             grind)
          | exact resolve b3e15 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e107 : y = (σ x) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e39 (σ x)
             grind)
          | exact superpose b3e39 b3e22
          | exact resolve b3e22 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e118 : x = (τ y) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e107
             grind)
          | exact superpose b3e107 b3e13
          | exact resolve b3e13 b3e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e107
        have b3e358 : ∀ X0 : G, y = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e73 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e359 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e358 X0
             have j1 := b3e101 X0 X0
             grind)
          | (have r₁ := b3e358 X0
             have r₂ := b3e101 X0 x
             grind)
          | (have r₁ := b3e358 y
             have r₂ := b3e101 y x
             grind)
          | exact resolve b3e358 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101 b3e358
        have b3e360 : ∀ X0 : G, y = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e359 X0
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e359
          | exact resolve b3e359 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e359
        have b3e367 : ∀ X0 : G, y = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e360 (σ X0)
             grind)
          | exact superpose b3e360 b3e18
          | exact resolve b3e18 b3e360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e376 : y = (σ y) := by
          first
          | (have i₁ := b3e367 x
             have i₂ := b3e360 x
             grind)
          | exact superpose b3e360 b3e367
          | exact resolve b3e367 b3e360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e360 b3e367
        have b3e389 : y = (τ y) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e376
             grind)
          | exact superpose b3e376 b3e13
          | exact resolve b3e13 b3e376
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e376
        have b3e390 : x = y := by
          first
          | (have i₁ := b3e389
             have i₂ := b3e118
             grind)
          | exact superpose b3e118 b3e389
          | exact resolve b3e389 b3e118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e118 b3e389
        have b3e395 : False := by grind
        exact b3e395
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
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
          have b4e37 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op y (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 X0) y X1
               have i₂ := b4e34 X0
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b4e44 X0 x
               have i₂ := b4e34 x
               grind)
            | exact superpose b4e34 b4e44
            | exact resolve b4e44 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e44
          have b4e46 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b4e45 X0
               have i₂ := b4e37 X0 X0
               grind)
            | exact superpose b4e37 b4e45
            | exact resolve b4e45 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e45
          have b4e47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (M.op X0 X0) X1
               have i₂ := b4e13 X0 X0 X0
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X0 X0) X1
               grind)
            | (have r₁ := b4e16 (M.op x x) X1
               have r₂ := b4e13 x x x
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e51 : ∀ X1 : G, (M.op X1 y) = (k y X1) := by
            intro X1
            first
            | (have i₁ := b4e50 x X1
               have i₂ := b4e46 x
               grind)
            | exact superpose b4e46 b4e50
            | exact resolve b4e50 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e132 : y = (σ y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e46 (σ x)
               grind)
            | exact superpose b4e46 b4e24
            | exact resolve b4e24 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e139 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e132
               grind)
            | exact superpose b4e132 b4e20
            | exact resolve b4e20 b4e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e142 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e132
               grind)
            | exact superpose b4e132 b4e19
            | exact resolve b4e19 b4e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132
          have b4e144 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e142 X0
               have i₂ := b4e51 (σ X0)
               grind)
            | exact superpose b4e51 b4e142
            | exact resolve b4e142 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142
          have b4e145 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e144 X0
               have i₂ := b4e51 X0
               grind)
            | exact superpose b4e51 b4e144
            | exact resolve b4e144 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e144
          have b4e394 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e139
               have i₂ := b4e145 x
               grind)
            | exact superpose b4e145 b4e139
            | (have r₁ := b4e139
               have r₂ := b4e145 x
               grind)
            | exact resolve b4e139 b4e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e139 b4e145
          have b4e399 : False := by grind
          exact b4e399
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e33 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
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
          have b5e35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op y (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 X0) y X1
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b5e40 X0 x
               have i₂ := b5e33 x
               grind)
            | exact superpose b5e33 b5e40
            | exact resolve b5e40 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e40
          have b5e42 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b5e41 X0
               have i₂ := b5e35 X0 X0
               grind)
            | exact superpose b5e35 b5e41
            | exact resolve b5e41 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e41
          have b5e80 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e18 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e83 : ∀ X0 X1 : G, X0 ≠ X1 ∨ y = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e80 X0 X1
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e80
            | (have j0 := b5e80 X0 X1
               grind)
            | (have r₁ := b5e80 (M.op X0 X0) y
               have r₂ := b5e42 X0
               grind)
            | (have r₁ := b5e80 y (M.op X0 X0)
               have r₂ := b5e42 X0
               grind)
            | exact resolve b5e80 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e116 : ∀ X0 X1 : G, y ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e16
            | (have j0 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e16 y X1
               have r₂ := b5e42 y
               grind)
            | exact resolve b5e16 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e122 : y ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e42 (σ x)
               grind)
            | exact superpose b5e42 b5e24
            | exact resolve b5e24 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e240 : ∀ X0 : G, y = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e83 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e241 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e240 X0
               have j1 := b5e116 X0 X0
               grind)
            | (have r₁ := b5e240 X0
               have r₂ := b5e116 X0 x
               grind)
            | (have r₁ := b5e240 y
               have r₂ := b5e116 y x
               grind)
            | exact resolve b5e240 b5e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116 b5e240
          have b5e242 : ∀ X0 : G, y = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e241 X0
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e241
            | exact resolve b5e241 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e241
          have b5e250 : ∀ X0 : G, y = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e242 (σ X0)
               grind)
            | exact superpose b5e242 b5e19
            | exact resolve b5e19 b5e242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e257 : y = (σ y) := by
            first
            | (have i₁ := b5e250 x
               have i₂ := b5e242 x
               grind)
            | exact superpose b5e242 b5e250
            | exact resolve b5e250 b5e242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e242 b5e250
          have b5e262 : False := by grind
          exact b5e262
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ x) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X0 X0) (σ x) X1
             have i₂ := b6e26 X0
             grind)
          | exact superpose b6e26 b6e12
          | exact resolve b6e12 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e33 X0 x
             have i₂ := b6e26 x
             grind)
          | exact superpose b6e26 b6e33
          | exact resolve b6e33 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26 b6e33
        have b6e35 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
          intro X0
          first
          | (have i₁ := b6e34 X0
             have i₂ := b6e28 X0 X0
             grind)
          | exact superpose b6e28 b6e34
          | exact resolve b6e34 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e34
        have b6e43 : ∀ X0 X1 : G, (σ x) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e15
          | (have j0 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e15 (σ x) X1
             have r₂ := b6e35 (σ x)
             grind)
          | exact resolve b6e15 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : x ≠ (σ x) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e35 x
             grind)
          | exact superpose b6e35 b6e20
          | exact resolve b6e20 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e70 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e17 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e72 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (σ x) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e70 X0 X1
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e70
          | (have j0 := b6e70 X0 X1
             grind)
          | (have r₁ := b6e70 (M.op X0 X0) (σ x)
             have r₂ := b6e35 X0
             grind)
          | (have r₁ := b6e70 (σ x) (M.op X0 X0)
             have r₂ := b6e35 X0
             grind)
          | exact resolve b6e70 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e206 : ∀ X0 : G, (σ x) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e72 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e207 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e206 X0
             have j1 := b6e43 X0 X0
             grind)
          | (have r₁ := b6e206 X0
             have r₂ := b6e43 X0 x
             grind)
          | (have r₁ := b6e206 (σ x)
             have r₂ := b6e43 (σ x) x
             grind)
          | exact resolve b6e206 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e206
        have b6e208 : ∀ X0 : G, (σ x) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b6e207 X0
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e207
          | exact resolve b6e207 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e207
        have b6e212 : ∀ X0 : G, (σ x) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e208 (σ X0)
             grind)
          | exact superpose b6e208 b6e18
          | exact resolve b6e18 b6e208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e221 : (σ x) = (σ (σ x)) := by
          first
          | (have i₁ := b6e212 x
             have i₂ := b6e208 x
             grind)
          | exact superpose b6e208 b6e212
          | exact resolve b6e212 b6e208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e208 b6e212
        have b6e231 : (σ x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (σ x)
             have i₂ := b6e221
             grind)
          | exact superpose b6e221 b6e13
          | exact resolve b6e13 b6e221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e221
        have b6e232 : x = (σ x) := by
          first
          | (have i₁ := b6e231
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e231
          | exact resolve b6e231 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e231
        have b6e236 : False := by grind
        exact b6e236
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b7e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b7e33 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) (σ x) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ y) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X0 X0) (σ y) X1
               have i₂ := b7e33 X0
               grind)
            | exact superpose b7e33 b7e13
            | exact resolve b7e13 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e40 X0 x
               have i₂ := b7e33 x
               grind)
            | exact superpose b7e33 b7e40
            | exact resolve b7e40 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e40
          have b7e42 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e41 X0
               have i₂ := b7e35 X0 X0
               grind)
            | exact superpose b7e35 b7e41
            | exact resolve b7e41 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e41
          have b7e49 : ∀ X0 X1 : G, (σ y) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e42 X0
               grind)
            | exact superpose b7e42 b7e16
            | (have j0 := b7e16 X0 X1
               grind)
            | (have r₁ := b7e16 (σ y) X1
               have r₂ := b7e42 (σ y)
               grind)
            | exact resolve b7e16 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e53 : y ≠ (σ y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e42 x
               grind)
            | exact superpose b7e42 b7e22
            | exact resolve b7e22 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e85 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e18 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (σ y) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e85 X0 X1
               have i₂ := b7e42 X0
               grind)
            | exact superpose b7e42 b7e85
            | (have j0 := b7e85 X0 X1
               grind)
            | (have r₁ := b7e85 (M.op X0 X0) (σ y)
               have r₂ := b7e42 X0
               grind)
            | (have r₁ := b7e85 (σ y) (M.op X0 X0)
               have r₂ := b7e42 X0
               grind)
            | exact resolve b7e85 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e247 : ∀ X0 : G, (σ y) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e87 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e248 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e247 X0
               have j1 := b7e49 X0 X0
               grind)
            | (have r₁ := b7e247 X0
               have r₂ := b7e49 X0 x
               grind)
            | (have r₁ := b7e247 (σ y)
               have r₂ := b7e49 (σ y) x
               grind)
            | exact resolve b7e247 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49 b7e247
          have b7e249 : ∀ X0 : G, (σ y) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b7e248 X0
               have i₂ := b7e42 X0
               grind)
            | exact superpose b7e42 b7e248
            | exact resolve b7e248 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42 b7e248
          have b7e259 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b7e32 (σ X0) X0
               have i₂ := b7e249 (σ X0)
               grind)
            | exact superpose b7e249 b7e32
            | exact resolve b7e32 b7e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e264 : ∀ X0 : G, (k X0 X0) = (τ (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e259 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e259
            | exact resolve b7e259 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e259
          have b7e269 : ∀ X0 : G, y = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b7e264 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e264
            | exact resolve b7e264 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e264
          have b7e283 : y = (σ y) := by
            first
            | (have i₁ := b7e249 x
               have i₂ := b7e269 x
               grind)
            | exact superpose b7e269 b7e249
            | exact resolve b7e249 b7e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e249 b7e269
          have b7e292 : False := by grind
          exact b7e292
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e82 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ x) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e93 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e82 X0
               grind)
            | (have r₁ := b8e82 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e82 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e93 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93
          have b8e185 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e184
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e184
            | exact resolve b8e184 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e264 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e185
               grind)
            | exact superpose b8e185 b8e20
            | exact resolve b8e20 b8e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185
          have b8e310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e264
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e264
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e264 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e264
          have b8e311 : x = (M.op x x) ∨ y = (M.op x x) := by grind
          clear b8e310
          have b8e313 : y = (M.op x x) := by
            first
            | (have r₁ := b8e311
               have r₂ := b8e21
               grind)
            | exact resolve b8e311 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e311
          have b8e315 : False := by grind
          exact b8e315

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation3756 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3756 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op x (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op X0 X0) x X1
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e11
        | exact resolve b0e11 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) := by
        intro X0
        first
        | (have i₁ := b0e37 X0 x
           have i₂ := b0e27 x
           grind)
        | exact superpose b0e27 b0e37
        | exact resolve b0e37 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e37
      have b0e39 : ∀ X0 : G, (M.op X0 X0) = x := by
        intro X0
        first
        | (have i₁ := b0e38 X0
           have i₂ := b0e30 X0 X0
           grind)
        | exact superpose b0e30 b0e38
        | exact resolve b0e38 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e40 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
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
      have b0e45 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e40 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e54 : x = (σ x) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e39 (σ x)
           grind)
        | exact superpose b0e39 b0e20
        | exact resolve b0e20 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e68 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e54
           grind)
        | exact superpose b0e54 b0e18
        | exact resolve b0e18 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e54
           grind)
        | exact superpose b0e54 b0e17
        | exact resolve b0e17 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e73 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) := by
        intro X0
        first
        | (have i₁ := b0e71 X0
           have i₂ := b0e45 (σ X0)
           grind)
        | exact superpose b0e45 b0e71
        | exact resolve b0e71 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71
      have b0e74 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e73 X0
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e73
        | exact resolve b0e73 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e73
      have b0e372 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X0)) x) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e74 (M.op X1 X0)
           have i₂ := b0e30 X0 X1
           grind)
        | exact superpose b0e30 b0e74
        | exact resolve b0e74 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1987 : ∀ X0 : G, (M.op (M.op (σ X0) x) x) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e372 x X0
           have i₂ := b0e74 X0
           grind)
        | exact superpose b0e74 b0e372
        | exact resolve b0e372 b0e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74 b0e372
      have b0e2011 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e1987 X0
           have i₂ := b0e30 x (σ X0)
           grind)
        | exact superpose b0e30 b0e1987
        | exact resolve b0e1987 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e1987
      have b0e2112 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e68
           have i₂ := b0e2011 y
           grind)
        | exact superpose b0e2011 b0e68
        | (have r₁ := b0e68
           have r₂ := b0e2011 y
           grind)
        | exact resolve b0e68 b0e2011
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68 b0e2011
      have b0e2132 : False := by grind
      exact b0e2132
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op x (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op X0 X0) x X1
             have i₂ := b1e25 X0
             grind)
          | exact superpose b1e25 b1e12
          | exact resolve b1e12 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b1e35 X0 x
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e35
          | exact resolve b1e35 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e35
        have b1e37 : ∀ X0 : G, (M.op X0 X0) = x := by
          intro X0
          first
          | (have i₁ := b1e36 X0
             have i₂ := b1e28 X0 X0
             grind)
          | exact superpose b1e28 b1e36
          | exact resolve b1e36 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e36
        have b1e38 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
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
        have b1e43 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e52 : x ≠ (σ x) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e37 (σ x)
             grind)
          | exact superpose b1e37 b1e21
          | exact resolve b1e21 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : x = (σ y) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e37 (σ y)
             grind)
          | exact superpose b1e37 b1e22
          | exact resolve b1e22 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e118 : ∀ X0 : G, (σ (k y X0)) = (k x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 y X0
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e18
          | exact resolve b1e18 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e119 : y = (τ x) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e13
          | exact resolve b1e13 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e120 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) x) := by
          intro X0
          first
          | (have i₁ := b1e118 X0
             have i₂ := b1e43 (σ X0)
             grind)
          | exact superpose b1e43 b1e118
          | exact resolve b1e118 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e118
        have b1e277 : ∀ X0 : G, (k y X0) = (τ (M.op (σ X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e13 (k y X0)
             have i₂ := b1e120 X0
             grind)
          | exact superpose b1e120 b1e13
          | exact resolve b1e13 b1e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120
        have b1e344 : (k y y) = (τ (M.op x x)) := by
          first
          | (have i₁ := b1e277 y
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e277
          | exact resolve b1e277 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e277
        have b1e352 : (τ x) = (k y y) := by
          first
          | (have i₁ := b1e344
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e344
          | exact resolve b1e344 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e344
        have b1e353 : y = (k y y) := by
          first
          | (have i₁ := b1e352
             have i₂ := b1e119
             grind)
          | exact superpose b1e119 b1e352
          | exact resolve b1e352 b1e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e119 b1e352
        have b1e362 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e353
             grind)
          | exact superpose b1e353 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e353
        have b1e363 : y = (M.op y y) := by grind
        clear b1e362
        have b1e365 : x = y := by
          first
          | (have i₁ := b1e363
             have i₂ := b1e37 y
             grind)
          | exact superpose b1e37 b1e363
          | exact resolve b1e363 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e363
        have b1e379 : x = (σ x) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e365
             grind)
          | exact superpose b1e365 b1e53
          | exact resolve b1e53 b1e365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e365
        have b1e386 : False := by grind
        exact b1e386
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b2e25 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 x x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op x (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op X0 X0) x X1
             have i₂ := b2e25 X0
             grind)
          | exact superpose b2e25 b2e12
          | exact resolve b2e12 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b2e32 X0 x
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e32
          | exact resolve b2e32 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e32
        have b2e34 : ∀ X0 : G, (M.op X0 X0) = x := by
          intro X0
          first
          | (have i₁ := b2e33 X0
             have i₂ := b2e27 X0 X0
             grind)
          | exact superpose b2e27 b2e33
          | exact resolve b2e33 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e33
        have b2e42 : ∀ X0 X1 : G, x ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e15
          | (have j0 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e15 x X1
             have r₂ := b2e34 x
             grind)
          | exact resolve b2e15 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46 : x ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e34 (σ x)
             grind)
          | exact superpose b2e34 b2e21
          | exact resolve b2e21 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e70 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
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
        have b2e80 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e70 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e91 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ x = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e80 X0 X1 X2
             have i₂ := b2e34 X2
             grind)
          | exact superpose b2e34 b2e80
          | (have j0 := b2e80 X0 X1 X2
             grind)
          | exact resolve b2e80 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e409 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b2e91 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e410 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b2e409 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e409
        have b2e414 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e410 X0
             have j1 := b2e42 X0 X0
             grind)
          | (have r₁ := b2e410 X0
             have r₂ := b2e42 X0 x
             grind)
          | (have r₁ := b2e410 x
             have r₂ := b2e42 x x
             grind)
          | exact resolve b2e410 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e410
        have b2e418 : ∀ X0 : G, x = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e414 X0
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e414
          | exact resolve b2e414 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e414
        have b2e443 : ∀ X0 : G, x = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e418 (σ X0)
             grind)
          | exact superpose b2e418 b2e18
          | exact resolve b2e18 b2e418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e455 : x = (σ x) := by
          first
          | (have i₁ := b2e443 x
             have i₂ := b2e418 x
             grind)
          | exact superpose b2e418 b2e443
          | exact resolve b2e443 b2e418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e418 b2e443
        have b2e462 : False := by grind
        exact b2e462
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 y y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op y (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op X0 X0) y X1
             have i₂ := b3e25 X0
             grind)
          | exact superpose b3e25 b3e12
          | exact resolve b3e12 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
          intro X0
          first
          | (have i₁ := b3e35 X0 x
             have i₂ := b3e25 x
             grind)
          | exact superpose b3e25 b3e35
          | exact resolve b3e35 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e35
        have b3e37 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b3e36 X0
             have i₂ := b3e28 X0 X0
             grind)
          | exact superpose b3e28 b3e36
          | exact resolve b3e36 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e36
        have b3e48 : ∀ X0 X1 : G, y ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e37 X0
             grind)
          | exact superpose b3e37 b3e15
          | (have j0 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e15 y X1
             have r₂ := b3e37 y
             grind)
          | exact resolve b3e15 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : y = (σ x) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e37 (σ x)
             grind)
          | exact superpose b3e37 b3e22
          | exact resolve b3e22 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e37 x
             grind)
          | exact superpose b3e37 b3e20
          | exact resolve b3e20 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e78 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
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
        have b3e84 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e78 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e91 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ y = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e84 X0 X1 X2
             have i₂ := b3e37 X2
             grind)
          | exact superpose b3e37 b3e84
          | (have j0 := b3e84 X0 X1 X2
             grind)
          | exact resolve b3e84 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e113 : x = (τ y) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e13
          | exact resolve b3e13 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e425 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e91 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91
        have b3e426 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e425 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e425
        have b3e430 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e426 X0
             have j1 := b3e48 X0 X0
             grind)
          | (have r₁ := b3e426 X0
             have r₂ := b3e48 X0 x
             grind)
          | (have r₁ := b3e426 y
             have r₂ := b3e48 y x
             grind)
          | exact resolve b3e426 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e426
        have b3e435 : ∀ X0 : G, y = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e430 X0
             have i₂ := b3e37 X0
             grind)
          | exact superpose b3e37 b3e430
          | exact resolve b3e430 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e430
        have b3e451 : ∀ X0 : G, y = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e435 (σ X0)
             grind)
          | exact superpose b3e435 b3e18
          | exact resolve b3e18 b3e435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e460 : y = (σ y) := by
          first
          | (have i₁ := b3e451 x
             have i₂ := b3e435 x
             grind)
          | exact superpose b3e435 b3e451
          | exact resolve b3e451 b3e435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e435 b3e451
        have b3e511 : y = (τ y) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e460
             grind)
          | exact superpose b3e460 b3e13
          | exact resolve b3e13 b3e460
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e460
        have b3e512 : x = y := by
          first
          | (have i₁ := b3e511
             have i₂ := b3e113
             grind)
          | exact superpose b3e113 b3e511
          | exact resolve b3e511 b3e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e113 b3e511
        have b3e518 : False := by grind
        exact b3e518
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op y (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 X0) y X1
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b4e41 X0 x
               have i₂ := b4e31 x
               grind)
            | exact superpose b4e31 b4e41
            | exact resolve b4e41 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e41
          have b4e43 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b4e42 X0
               have i₂ := b4e34 X0 X0
               grind)
            | exact superpose b4e34 b4e42
            | exact resolve b4e42 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e42
          have b4e44 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) := by
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
          have b4e49 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b4e44 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e59 : y = (σ y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e43 (σ y)
               grind)
            | exact superpose b4e43 b4e24
            | exact resolve b4e24 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e127 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e59
               grind)
            | exact superpose b4e59 b4e20
            | exact resolve b4e20 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e59
               grind)
            | exact superpose b4e59 b4e19
            | exact resolve b4e19 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e132 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e130 X0
               have i₂ := b4e49 (σ X0)
               grind)
            | exact superpose b4e49 b4e130
            | exact resolve b4e130 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e133 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e132 X0
               have i₂ := b4e49 X0
               grind)
            | exact superpose b4e49 b4e132
            | exact resolve b4e132 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e132
          have b4e368 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e127
               have i₂ := b4e133 x
               grind)
            | exact superpose b4e133 b4e127
            | (have r₁ := b4e127
               have r₂ := b4e133 x
               grind)
            | exact resolve b4e127 b4e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127 b4e133
          have b4e373 : False := by grind
          exact b4e373
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b5e31 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 y y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op y (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 X0) y X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b5e38 X0 x
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e38
            | exact resolve b5e38 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e38
          have b5e40 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b5e39 X0
               have i₂ := b5e33 X0 X0
               grind)
            | exact superpose b5e33 b5e39
            | exact resolve b5e39 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e39
          have b5e48 : ∀ X0 X1 : G, y ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e40 X0
               grind)
            | exact superpose b5e40 b5e16
            | (have j0 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e16 y X1
               have r₂ := b5e40 y
               grind)
            | exact resolve b5e16 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : y ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e40 (σ y)
               grind)
            | exact superpose b5e40 b5e24
            | exact resolve b5e24 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
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
          have b5e88 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e77 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e100 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ y = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e88 X0 X1 X2
               have i₂ := b5e40 X2
               grind)
            | exact superpose b5e40 b5e88
            | (have j0 := b5e88 X0 X1 X2
               grind)
            | exact resolve b5e88 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e387 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ y = X0 := by
            intro X0
            first
            | (have j0 := b5e100 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100
          have b5e388 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ y = X0 := by
            intro X0
            first
            | (have j0 := b5e387 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e387
          have b5e392 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e388 X0
               have j1 := b5e48 X0 X0
               grind)
            | (have r₁ := b5e388 X0
               have r₂ := b5e48 X0 x
               grind)
            | (have r₁ := b5e388 y
               have r₂ := b5e48 y x
               grind)
            | exact resolve b5e388 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e388
          have b5e396 : ∀ X0 : G, y = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e392 X0
               have i₂ := b5e40 X0
               grind)
            | exact superpose b5e40 b5e392
            | exact resolve b5e392 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e392
          have b5e420 : ∀ X0 : G, y = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e396 (σ X0)
               grind)
            | exact superpose b5e396 b5e19
            | exact resolve b5e19 b5e396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e430 : y = (σ y) := by
            first
            | (have i₁ := b5e420 x
               have i₂ := b5e396 x
               grind)
            | exact superpose b5e396 b5e420
            | exact resolve b5e420 b5e396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e396 b5e420
          have b5e436 : False := by grind
          exact b5e436
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e25 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ x) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X0 X0) (σ x) X1
             have i₂ := b6e25 X0
             grind)
          | exact superpose b6e25 b6e12
          | exact resolve b6e12 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e32 X0 x
             have i₂ := b6e25 x
             grind)
          | exact superpose b6e25 b6e32
          | exact resolve b6e32 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25 b6e32
        have b6e34 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
          intro X0
          first
          | (have i₁ := b6e33 X0
             have i₂ := b6e27 X0 X0
             grind)
          | exact superpose b6e27 b6e33
          | exact resolve b6e33 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27 b6e33
        have b6e35 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
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
        have b6e38 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e101 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e38 (σ X0)
             grind)
          | exact superpose b6e38 b6e18
          | exact resolve b6e18 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e159 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e34 (σ x)
             have i₂ := b6e101 x
             grind)
          | exact superpose b6e101 b6e34
          | exact resolve b6e34 b6e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34 b6e101
        have b6e218 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e159
             grind)
          | exact superpose b6e159 b6e13
          | exact resolve b6e13 b6e159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e159
        have b6e220 : x = (k x x) := by
          first
          | (have i₁ := b6e218
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e218
          | exact resolve b6e218 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e218
        have b6e253 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e220
             grind)
          | exact superpose b6e220 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e220
        have b6e254 : x = (M.op x x) := by grind
        clear b6e253
        have b6e256 : False := by grind
        exact b6e256
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b7e31 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) (σ y) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ y) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X0 X0) (σ y) X1
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e13
            | exact resolve b7e13 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e38 X0 x
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e38
            | exact resolve b7e38 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e38
          have b7e40 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e39 X0
               have i₂ := b7e33 X0 X0
               grind)
            | exact superpose b7e33 b7e39
            | exact resolve b7e39 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e39
          have b7e41 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
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
          have b7e44 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e41 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e117 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e44 (σ X0)
               grind)
            | exact superpose b7e44 b7e19
            | exact resolve b7e19 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e228 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e40 (σ y)
               have i₂ := b7e117 y
               grind)
            | exact superpose b7e117 b7e40
            | exact resolve b7e40 b7e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e117
          have b7e248 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e228
               grind)
            | exact superpose b7e228 b7e14
            | exact resolve b7e14 b7e228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e228
          have b7e250 : y = (k y y) := by
            first
            | (have i₁ := b7e248
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e248
            | exact resolve b7e248 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e248
          have b7e262 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e250
               grind)
            | exact superpose b7e250 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e250
          have b7e263 : y = (M.op y y) := by grind
          clear b7e262
          have b7e265 : False := by grind
          exact b7e265
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
          have b8e78 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e84 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e231 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e84 (σ X0)
               grind)
            | exact superpose b8e84 b8e19
            | (have j1 := b8e84 (σ X0)
               grind)
            | exact resolve b8e19 b8e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e8459 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e231 x
               grind)
            | exact superpose b8e231 b8e20
            | (have j1 := b8e231 x
               grind)
            | exact resolve b8e20 b8e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231
          have b8e8739 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e8459
               have r₂ := b8e23
               grind)
            | exact resolve b8e8459 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8459
          have b8e8841 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e8739
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e8739
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e8739 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8739
          have b8e8853 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e8841
          have b8e8859 : y = (M.op y y) := by
            first
            | (have r₁ := b8e8853
               have r₂ := b8e21
               grind)
            | exact resolve b8e8853 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8853
          have b8e8860 : False := by grind
          exact b8e8860

/-- `Equation4271`: `x ◇ (x ◇ x) = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4271 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4271 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4271.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x x) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
      have b0e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b0e30 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 x X0 X1
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 (σ x) X0 X1
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : (M.op x y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b0e30 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e30
        | exact resolve b0e30 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
        intro X0 X1
        grind
      have b0e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X0) (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e33 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e33
        | exact resolve b0e33 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e65 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e10
        | exact resolve b0e10 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e70 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e65 X0 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e65
        | exact resolve b0e65 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e88 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e24 X1 X0
           have i₂ := b0e14 X0 (τ X1)
           grind)
        | exact superpose b0e14 b0e24
        | (have j1 := b0e14 X0 (τ X1)
           grind)
        | exact resolve b0e24 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e93 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e97 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e70 (σ x)
           grind)
        | exact superpose b0e70 b0e16
        | exact resolve b0e16 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e211 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e29
        | exact resolve b0e29 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e214 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X0 X1
           have i₂ := b0e14 X0 (σ X1)
           grind)
        | exact superpose b0e14 b0e29
        | (have j1 := b0e14 X0 (σ X1)
           grind)
        | exact resolve b0e29 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e264 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e52 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e270 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      have b0e300 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 y) ∨ (M.op X1 X2) = (k X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e264 X0 (M.op X1 X2)
           have i₂ := b0e65 X0 X1 X2
           grind)
        | exact superpose b0e65 b0e264
        | (have j0 := b0e264 X0 (M.op X1 X2)
           grind)
        | (have r₁ := b0e264 X0 (M.op X0 y)
           have r₂ := b0e65 X0 X0 y
           grind)
        | exact resolve b0e264 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e264
      have b0e630 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1
           have i₂ := b0e56 X0 X1
           grind)
        | exact superpose b0e56 b0e11
        | (have j1 := b0e56 X0 X1
           grind)
        | exact resolve b0e11 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e632 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X2
           have i₂ := b0e56 X0 X2
           grind)
        | exact superpose b0e56 b0e15
        | (have j1 := b0e56 X0 X2
           grind)
        | exact resolve b0e15 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e1502 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e88 X0 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e88
        | exact resolve b0e88 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1550 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 X1
           have i₂ := b0e88 X0 X1
           grind)
        | exact superpose b0e88 b0e12
        | (have j1 := b0e88 X0 X1
           grind)
        | exact resolve b0e12 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e1591 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e1502 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e1502
        | (have j0 := b0e1502 X0 X1
           grind)
        | exact resolve b0e1502 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1502
      have b0e3485 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e630 x X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e630
        | (have j0 := b0e630 x X0
           grind)
        | exact resolve b0e630 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e630
      have b0e3615 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e3485 X0
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e3485
        | (have j0 := b0e3485 X0
           grind)
        | exact resolve b0e3485 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3485
      have b0e4349 : ∀ X0 : G, (M.op (σ x) X0) = (σ (k x (τ X0))) ∨ (τ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e3615 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e3615
        | (have j0 := b0e3615 (τ X0)
           grind)
        | exact resolve b0e3615 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4386 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (k x X0))) ∨ y = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e65 X1 (σ x) (σ X0)
           have i₂ := b0e3615 X0
           grind)
        | exact superpose b0e3615 b0e65
        | (have j1 := b0e3615 X0
           grind)
        | exact resolve b0e65 b0e3615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4405 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (τ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e4349 X0
           have i₂ := b0e24 X0 x
           grind)
        | exact superpose b0e24 b0e4349
        | (have j0 := b0e4349 X0
           grind)
        | exact resolve b0e4349 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4349
      have b0e4569 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e4386 X0 X1
           have i₂ := b0e1591 X0 x
           grind)
        | exact superpose b0e1591 b0e4386
        | (have j0 := b0e4386 X0 X1
           have j1 := b0e1591 X0 x
           grind)
        | exact resolve b0e4386 b0e1591
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1591 b0e4386
      have b0e4623 : ∀ X0 X1 : G, y = X0 ∨ (M.op X1 y) = (M.op X1 (σ (M.op x X0))) ∨ y = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e4569 X0 X1
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e4569
        | (have j0 := b0e4569 X0 X1
           grind)
        | exact resolve b0e4569 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4569
      have b0e4624 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op x X0))) ∨ y = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e4623 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4623
      have b0e5356 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (σ (M.op x y))) ∨ (M.op X1 X2) = y := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e4624 (M.op X1 X2) X0
           have i₂ := b0e65 x X1 X2
           grind)
        | exact superpose b0e65 b0e4624
        | (have j0 := b0e4624 y X0
           grind)
        | exact resolve b0e4624 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4624
      have b0e8241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      clear b0e632
      have b0e27440 : (τ (M.op x y)) = (k (τ x) y) ∨ (σ y) = (M.op x x) := by
        first
        | (have i₁ := b0e214 x y
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e214
        | (have j0 := b0e214 x y
           grind)
        | exact resolve b0e214 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e214
      have b0e28068 : (τ (M.op x y)) = (k (τ x) y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e27440
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e27440
        | exact resolve b0e27440 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27440
      have b0e28610 : (M.op x y) = (σ (k (τ x) y)) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e28068
           grind)
        | exact superpose b0e28068 b0e12
        | exact resolve b0e12 b0e28068
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28068
      have b0e28639 : (M.op x y) = (k x (σ y)) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e28610
           have i₂ := b0e23 x y
           grind)
        | exact superpose b0e23 b0e28610
        | exact resolve b0e28610 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e28610
      have b0e28735 : ∀ X0 : G, (M.op X0 y) = (k X0 (M.op X0 y)) := by
        intro X0
        first
        | (have j0 := b0e300 X0 X0 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e300
      have b0e28825 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (k X0 (τ (M.op (σ X0) y))) := by
        intro X0
        first
        | (have i₁ := b0e93 X0 (M.op (σ X0) y)
           have i₂ := b0e28735 (σ X0)
           grind)
        | exact superpose b0e28735 b0e93
        | exact resolve b0e93 b0e28735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31737 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (σ (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op X0 (τ X1))
           have i₂ := b0e1550 X0 X1
           grind)
        | exact superpose b0e1550 b0e11
        | (have j1 := b0e1550 X0 X1
           grind)
        | exact resolve b0e11 b0e1550
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1550
      have b0e31854 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (σ (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e31737 X0 X1
           have i₂ := b0e93 X0 X1
           grind)
        | exact superpose b0e93 b0e31737
        | (have j0 := b0e31737 X0 X1
           grind)
        | exact resolve b0e31737 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93 b0e31737
      have b0e65877 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e8241 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8241
      have b0e65878 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e65877 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65877
      have b0e65985 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e65878 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e65878
        | exact resolve b0e65878 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66132 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (k X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e65 X1 (σ X0) (σ X0)
           have i₂ := b0e65878 X0
           grind)
        | exact superpose b0e65878 b0e65
        | exact resolve b0e65 b0e65878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65878
      have b0e66217 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b0e65985 X0
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e65985
        | exact resolve b0e65985 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65985
      have b0e66233 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e66217 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e66217
        | exact resolve b0e66217 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66217
      have b0e66458 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e211 X0 X0
           have i₂ := b0e66233 (τ X0)
           grind)
        | exact superpose b0e66233 b0e211
        | exact resolve b0e211 b0e66233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66562 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e66458 X0
           have i₂ := b0e66233 X0
           grind)
        | exact superpose b0e66233 b0e66458
        | exact resolve b0e66458 b0e66233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66458
      have b0e67650 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e66132 X0 X1
           have i₂ := b0e66233 X0
           grind)
        | exact superpose b0e66233 b0e66132
        | exact resolve b0e66132 b0e66233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66132 b0e66233
      have b0e68261 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (τ X0) X1
           have i₂ := b0e66562 X0
           grind)
        | exact superpose b0e66562 b0e14
        | (have j0 := b0e14 (τ X0) X1
           grind)
        | exact resolve b0e14 b0e66562
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e68289 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e65 X1 (τ X0) (τ X0)
           have i₂ := b0e66562 X0
           grind)
        | exact superpose b0e66562 b0e65
        | exact resolve b0e65 b0e66562
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e68482 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e67650 (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e67650
        | exact resolve b0e67650 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67650
      have b0e68790 : (M.op (σ x) y) = (σ (k x (σ y))) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e3615 (σ y)
           have i₂ := b0e68482 (σ x)
           grind)
        | exact superpose b0e68482 b0e3615
        | (have j0 := b0e3615 (σ y)
           grind)
        | exact resolve b0e3615 b0e68482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68482
      have b0e77335 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e68790
           have i₂ := b0e28639
           grind)
        | exact superpose b0e28639 b0e68790
        | exact resolve b0e68790 b0e28639
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28639 b0e68790
      have b0e77369 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ y) := by grind
      clear b0e77335
      have b0e77383 : y = (σ y) := by
        first
        | (have r₁ := b0e77369
           have r₂ := b0e97
           grind)
        | exact resolve b0e77369 b0e97
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77369
      have b0e92257 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e211 X1 X0
           have i₂ := b0e31854 (τ X0) X1
           grind)
        | exact superpose b0e31854 b0e211
        | (have j1 := b0e31854 (τ X0) X1
           grind)
        | exact resolve b0e211 b0e31854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31854
      have b0e92319 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e92257 X0 X1
           have i₂ := b0e66562 X0
           grind)
        | exact superpose b0e66562 b0e92257
        | (have j0 := b0e92257 X0 X1
           grind)
        | exact resolve b0e92257 b0e66562
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66562 b0e92257
      have b0e92351 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e92319 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e92319
        | (have j0 := b0e92319 X0 X1
           grind)
        | exact resolve b0e92319 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92319
      have b0e99842 : ∀ X0 X1 : G, (M.op (σ x) y) = (σ (k x (M.op x y))) ∨ y = (M.op x y) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e3615 (M.op x y)
           have i₂ := b0e5356 (σ x) X0 X1
           grind)
        | exact superpose b0e5356 b0e3615
        | (have j0 := b0e3615 (M.op x y)
           have j1 := b0e5356 X0 x y
           grind)
        | exact resolve b0e3615 b0e5356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3615 b0e5356
      have b0e100118 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e99842 X0 X1
           have i₂ := b0e28735 x
           grind)
        | exact superpose b0e28735 b0e99842
        | (have j0 := b0e99842 x y
           grind)
        | exact resolve b0e99842 b0e28735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28735 b0e99842
      have b0e100137 : ∀ X0 X1 : G, y = (M.op x y) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have j0 := b0e100118 x y
           grind)
        | (have r₁ := b0e100118 X0 X1
           have r₂ := b0e97
           grind)
        | exact resolve b0e100118 b0e97
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100118
      have b0e100802 : y ≠ y ∨ y = (M.op x y) := by
        first
        | (have j0 := b0e100137 x y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100137
      have b0e100803 : y = (M.op x y) := by grind
      clear b0e100802
      have b0e100830 : (σ y) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e97
           have i₂ := b0e100803
           grind)
        | exact superpose b0e100803 b0e97
        | exact resolve b0e97 b0e100803
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97
      have b0e100894 : y ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e100830
           have i₂ := b0e77383
           grind)
        | exact superpose b0e77383 b0e100830
        | exact resolve b0e100830 b0e77383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100830
      have b0e108293 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e68261 (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e68261
        | (have j0 := b0e68261 (σ x) X0
           grind)
        | exact resolve b0e68261 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68261
      have b0e108423 : ∀ X0 : G, y = X0 ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e108293 X0
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e108293
        | (have j0 := b0e108293 X0
           grind)
        | exact resolve b0e108293 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108293
      have b0e108459 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e108423 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e108423
        | (have j0 := b0e108423 X0
           grind)
        | exact resolve b0e108423 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108423
      have b0e108653 : ∀ X0 : G, (k (τ x) X0) = (τ (M.op x (σ X0))) ∨ (σ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e29 x X0
           have i₂ := b0e108459 (σ X0)
           grind)
        | exact superpose b0e108459 b0e29
        | (have j1 := b0e108459 (σ X0)
           grind)
        | exact resolve b0e29 b0e108459
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e108658 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e24 X0 x
           have i₂ := b0e108459 (τ X0)
           grind)
        | exact superpose b0e108459 b0e24
        | (have j1 := b0e108459 (τ X0)
           grind)
        | exact resolve b0e24 b0e108459
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108459
      have b0e109505 : ∀ X0 : G, (τ (M.op x X0)) = (k (τ x) (τ X0)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e108653 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e108653
        | exact resolve b0e108653 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108653
      have b0e109576 : ∀ X0 : G, (τ (M.op x X0)) = (τ (k x X0)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e109505 X0
           have i₂ := b0e211 X0 x
           grind)
        | exact superpose b0e211 b0e109505
        | (have j0 := b0e109505 X0
           grind)
        | exact resolve b0e109505 b0e211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e211 b0e109505
      have b0e109798 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (M.op X0 X0)) ∨ y = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e108658 (M.op X0 X0)
           have i₂ := b0e68289 X0 x
           grind)
        | exact superpose b0e68289 b0e108658
        | (have j0 := b0e108658 (M.op X0 X0)
           grind)
        | exact resolve b0e108658 b0e68289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68289 b0e108658
      have b0e109829 : ∀ X0 : G, (σ y) = (k (σ x) (M.op X0 X0)) ∨ y = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e109798 X0
           have i₂ := b0e100803
           grind)
        | exact superpose b0e100803 b0e109798
        | (have j0 := b0e109798 X0
           grind)
        | exact resolve b0e109798 b0e100803
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109798
      have b0e109841 : ∀ X0 : G, y = (k (σ x) (M.op X0 X0)) ∨ y = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e109829 X0
           have i₂ := b0e77383
           grind)
        | exact superpose b0e77383 b0e109829
        | (have j0 := b0e109829 X0
           grind)
        | exact resolve b0e109829 b0e77383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109829
      have b0e110893 : ∀ X0 : G, y = (M.op (σ x) (M.op X0 X0)) ∨ y = (τ (M.op X0 X0)) ∨ y = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e4405 (M.op X0 X0)
           have i₂ := b0e109841 X0
           grind)
        | exact superpose b0e109841 b0e4405
        | (have j0 := b0e4405 (M.op X0 X0)
           have j1 := b0e109841 X0
           grind)
        | exact resolve b0e4405 b0e109841
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4405 b0e109841
      have b0e110907 : ∀ X0 : G, y = (M.op (σ x) (M.op X0 X0)) ∨ y = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e110893 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110893
      have b0e110920 : ∀ X0 : G, y = (M.op (σ x) (σ y)) ∨ y = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e110907 X0
           have i₂ := b0e31 X0 X0
           grind)
        | exact superpose b0e31 b0e110907
        | (have j0 := b0e110907 X0
           grind)
        | exact resolve b0e110907 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110907
      have b0e110946 : ∀ X0 : G, y = (M.op (σ x) y) ∨ y = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e110920 X0
           have i₂ := b0e62
           grind)
        | exact superpose b0e62 b0e110920
        | (have j0 := b0e110920 X0
           grind)
        | exact resolve b0e110920 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110920
      have b0e110969 : ∀ X0 : G, y = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e110946 X0
           grind)
        | (have r₁ := b0e110946 X0
           have r₂ := b0e100894
           grind)
        | exact resolve b0e110946 b0e100894
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110946
      have b0e111292 : ∀ X0 : G, y = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e270 X0
           have i₂ := b0e110969 (σ X0)
           grind)
        | exact superpose b0e110969 b0e270
        | exact resolve b0e270 b0e110969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e270
      have b0e111323 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e12 (M.op X0 X0)
           have i₂ := b0e110969 X0
           grind)
        | exact superpose b0e110969 b0e12
        | exact resolve b0e12 b0e110969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111325 : ∀ X0 X1 : G, (σ (k X0 y)) = (k (σ X0) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e24 (M.op X1 X1) X0
           have i₂ := b0e110969 X1
           grind)
        | exact superpose b0e110969 b0e24
        | exact resolve b0e24 b0e110969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110969
      have b0e111481 : ∀ X0 : G, (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e111323 X0
           have i₂ := b0e77383
           grind)
        | exact superpose b0e77383 b0e111323
        | exact resolve b0e111323 b0e77383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111323
      have b0e112720 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ y = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e111481 X0
           grind)
        | exact superpose b0e111481 b0e14
        | (have j0 := b0e14 X0 X1
           grind)
        | exact resolve b0e14 b0e111481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e112782 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ y = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e92351 X0 X1
           have i₂ := b0e111481 X0
           grind)
        | exact superpose b0e111481 b0e92351
        | (have j0 := b0e92351 X0 X1
           grind)
        | exact resolve b0e92351 b0e111481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92351 b0e111481
      have b0e125223 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (k X1 y)) ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e111325 X1 X2
           have i₂ := b0e14 X2 X0
           grind)
        | (have i₁ := b0e111325 X0 X1
           have i₂ := b0e14 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e14 b0e111325
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e111325 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111325
      have b0e125671 : ∀ X0 X1 X2 : G, (σ y) = (k (σ X1) X0) ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e125223 X0 X1 X2
           have i₂ := b0e111292 X1
           grind)
        | exact superpose b0e111292 b0e125223
        | (have j0 := b0e125223 X0 X1 X2
           grind)
        | exact resolve b0e125223 b0e111292
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111292 b0e125223
      have b0e125897 : ∀ X0 X1 X2 : G, y = (k (σ X1) X0) ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e125671 X0 X1 X2
           have i₂ := b0e77383
           grind)
        | exact superpose b0e77383 b0e125671
        | (have j0 := b0e125671 X0 X1 X2
           grind)
        | exact resolve b0e125671 b0e77383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125671
      have b0e159068 : ∀ X0 X1 X2 : G, (k X0 X1) = y ∨ (k X2 X1) = (M.op X2 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e125897 X1 (τ X0) X2
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e125897
        | (have j0 := b0e125897 X1 X1 X2
           grind)
        | exact resolve b0e125897 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125897
      have b0e160084 : ∀ X0 X1 : G, (M.op X0 X1) ≠ y ∨ (k X0 X1) = y := by
        intro X0 X1
        first
        | (have j0 := b0e159068 X0 X1 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e159068
      have b0e160600 : ∀ X0 X1 : G, y ≠ (M.op x y) ∨ y = (k x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e160084 x (M.op X0 X1)
           have i₂ := b0e30 X0 X1
           grind)
        | exact superpose b0e30 b0e160084
        | (have j0 := b0e160084 x y
           grind)
        | exact resolve b0e160084 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e160700 : ∀ X0 X1 : G, y = (k x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e160600 X0 X1
           grind)
        | (have r₁ := b0e160600 X0 X1
           have r₂ := b0e100803
           grind)
        | exact resolve b0e160600 b0e100803
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100803 b0e160600
      have b0e161153 : ∀ X0 X1 : G, y = (k x (τ (k X0 X1))) ∨ y = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e160700 (τ X0) (τ X1)
           have i₂ := b0e112782 X0 X1
           grind)
        | exact superpose b0e112782 b0e160700
        | (have j1 := b0e112782 X0 (k x (τ (k X0 X1)))
           grind)
        | exact resolve b0e160700 b0e112782
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112782 b0e160700
      have b0e172501 : ∀ X0 : G, y = (k x (τ (M.op x X0))) ∨ y = X0 ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e161153 x X0
           have i₂ := b0e109576 X0
           grind)
        | exact superpose b0e109576 b0e161153
        | (have j0 := b0e161153 X0 (k x (τ (M.op x X0)))
           have j1 := b0e109576 (k x (τ (M.op x X0)))
           grind)
        | exact resolve b0e161153 b0e109576
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109576 b0e161153
      have b0e172565 : ∀ X0 : G, y = (k x (τ (M.op x X0))) ∨ y = X0 := by
        intro X0
        first
        | (have j0 := b0e172501 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e172501
      have b0e175094 : ∀ X0 : G, (σ y) = (k (σ x) (M.op x X0)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e24 (M.op x X0) x
           have i₂ := b0e172565 X0
           grind)
        | exact superpose b0e172565 b0e24
        | (have j1 := b0e172565 X0
           grind)
        | exact resolve b0e24 b0e172565
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e172565
      have b0e175151 : ∀ X0 : G, y = (k (σ x) (M.op x X0)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e175094 X0
           have i₂ := b0e77383
           grind)
        | exact superpose b0e77383 b0e175094
        | (have j0 := b0e175094 (k (σ x) (M.op x X0))
           grind)
        | exact resolve b0e175094 b0e77383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e175094
      have b0e177712 : ∀ X0 : G, y = (M.op (σ x) (M.op x X0)) ∨ y = (M.op x X0) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e112720 (σ x) (M.op x X0)
           have i₂ := b0e175151 X0
           grind)
        | exact superpose b0e175151 b0e112720
        | (have j0 := b0e112720 X0 (M.op (σ x) (M.op x X0))
           have j1 := b0e175151 (M.op (σ x) (M.op x X0))
           grind)
        | exact resolve b0e112720 b0e175151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112720 b0e175151
      have b0e177756 : ∀ X0 : G, y = (M.op (σ x) (σ y)) ∨ y = (M.op x X0) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e177712 X0
           have i₂ := b0e31 x X0
           grind)
        | exact superpose b0e31 b0e177712
        | (have j0 := b0e177712 X0
           grind)
        | exact resolve b0e177712 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e177712
      have b0e177878 : ∀ X0 : G, y = (M.op (σ x) y) ∨ y = (M.op x X0) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e177756 X0
           have i₂ := b0e62
           grind)
        | exact superpose b0e62 b0e177756
        | (have j0 := b0e177756 X0
           grind)
        | exact resolve b0e177756 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62 b0e177756
      have b0e177909 : ∀ X0 : G, y = (M.op x X0) ∨ y = X0 := by
        intro X0
        first
        | (have j0 := b0e177878 X0
           grind)
        | (have r₁ := b0e177878 X0
           have r₂ := b0e100894
           grind)
        | (have r₁ := b0e177878 (M.op (σ x) y)
           have r₂ := b0e100894
           grind)
        | exact resolve b0e177878 b0e100894
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e177878
      have b0e178185 : ∀ X0 : G, y ≠ y ∨ y = (k x X0) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e160084 x X0
           have i₂ := b0e177909 X0
           grind)
        | exact superpose b0e177909 b0e160084
        | (have j0 := b0e160084 x X0
           have j1 := b0e177909 (k x X0)
           grind)
        | (have r₁ := b0e160084 x X0
           have r₂ := b0e177909 X0
           grind)
        | (have r₁ := b0e160084 X0 x
           have r₂ := b0e177909 (M.op X0 x)
           grind)
        | exact resolve b0e160084 b0e177909
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e160084 b0e177909
      have b0e178343 : ∀ X0 : G, y = (k x X0) ∨ y = X0 := by
        intro X0
        first
        | (have j0 := b0e178185 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e178185
      have b0e178698 : y = (τ (M.op (σ x) y)) ∨ y = (τ (M.op (σ x) y)) := by
        first
        | (have i₁ := b0e28825 x
           have i₂ := b0e178343 (τ (M.op (σ x) y))
           grind)
        | exact superpose b0e178343 b0e28825
        | (have j1 := b0e178343 (τ (M.op (σ x) y))
           grind)
        | exact resolve b0e28825 b0e178343
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28825 b0e178343
      have b0e178744 : y = (τ (M.op (σ x) y)) := by grind
      clear b0e178698
      have b0e178961 : (σ y) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e12 (M.op (σ x) y)
           have i₂ := b0e178744
           grind)
        | exact superpose b0e178744 b0e12
        | exact resolve b0e12 b0e178744
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e178744
      have b0e179073 : y = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e178961
           have i₂ := b0e77383
           grind)
        | exact superpose b0e77383 b0e178961
        | exact resolve b0e178961 b0e77383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77383 b0e178961
      have b0e179114 : False := by grind
      exact b0e179114
    · have b1e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op x x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : y = (k x y) := by grind
      have b1e44 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e18
           have i₂ := b1e14 (σ x) X0
           grind)
        | (have i₁ := b1e18
           have i₂ := b1e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b1e14 b1e18
        | (have j1 := b1e14 (σ x) X0
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e14 (σ x) (σ y)
           grind)
        | exact resolve b1e18 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e46 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
        intro X0 X1
        grind
      have b1e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e167 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b1e46 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e44 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44
      have b1e185 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e184
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e184
        | exact resolve b1e184 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e184
      have b1e186 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e185
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e185
        | exact resolve b1e185 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e185
      have b1e187 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e186
           grind)
        | exact superpose b1e186 b1e16
        | exact resolve b1e16 b1e186
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e186
      have b1e428 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e50 x x
           grind)
        | exact superpose b1e50 b1e18
        | (have j1 := b1e50 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e50 x y
           grind)
        | exact resolve b1e18 b1e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e925 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e428
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e428
        | (have j1 := b1e14 (σ x) (σ x)
           grind)
        | exact resolve b1e428 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e428
      have b1e941 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e925
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e925
        | exact resolve b1e925 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e925
      have b1e942 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b1e941
      have b1e945 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e942
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e942
        | exact resolve b1e942 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e942
      have b1e981 : (σ x) ≠ (σ y) ∨ x = y := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e945
           grind)
        | exact superpose b1e945 b1e18
        | exact resolve b1e18 b1e945
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e995 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e167 (σ x) (σ x)
           have i₂ := b1e945
           grind)
        | exact superpose b1e945 b1e167
        | (have j0 := b1e167 (σ x) (σ x)
           grind)
        | (have r₁ := b1e167 (σ x) (σ x)
           have r₂ := b1e945
           grind)
        | exact resolve b1e167 b1e945
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e167 b1e945
      have b1e996 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
      clear b1e995
      have b1e997 : (σ x) = (σ (k x x)) ∨ x = y := by
        first
        | (have i₁ := b1e996
           have i₂ := b1e15 x x
           grind)
        | exact superpose b1e15 b1e996
        | exact resolve b1e996 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e996
      have b1e1255 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e997
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e997
        | (have j1 := b1e14 x x
           grind)
        | exact resolve b1e997 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e997
      have b1e1300 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1255
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1255
        | exact resolve b1e1255 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1255
      have b1e1308 : x = y ∨ x = (M.op x x) := by
        first
        | (have r₁ := b1e1300
           have r₂ := b1e981
           grind)
        | exact resolve b1e1300 b1e981
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e981 b1e1300
      have b1e1310 : x = y ∨ x = y := by
        first
        | (have i₁ := b1e1308
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1308
        | exact resolve b1e1308 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1308
      have b1e1311 : x = y := by grind
      clear b1e1310
      have b1e1321 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e187
           have i₂ := b1e1311
           grind)
        | exact superpose b1e1311 b1e187
        | exact resolve b1e187 b1e1311
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e187
      have b1e1345 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e1321
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1321
        | exact resolve b1e1321 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1321
      have b1e1354 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e1345
           have i₂ := b1e1311
           grind)
        | exact superpose b1e1311 b1e1345
        | exact resolve b1e1345 b1e1311
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1311 b1e1345
      have b1e1355 : False := by grind
      exact b1e1355
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op x x) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : (σ y) = (k (σ x) (σ y)) := by grind
      have b2e21 : (σ y) = (σ (k x y)) := by
        first
        | (have i₁ := b2e20
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e20
        | exact resolve b2e20 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e26 : (k x y) = (τ (σ y)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e21
           grind)
        | exact superpose b2e21 b2e11
        | exact resolve b2e11 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e27 : y = (k x y) := by
        first
        | (have i₁ := b2e26
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e26
        | exact resolve b2e26 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26
      have b2e46 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
        intro X0 X1
        grind
      have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e14 (σ X0) (σ X1)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X0) (σ X1)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e51 : y = (M.op x y) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e27
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e27
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e27 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e54 : y = (M.op x y) := by
        first
        | (have r₁ := b2e51
           have r₂ := b2e17
           grind)
        | exact resolve b2e51 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e591 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e49 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e49
        | exact resolve b2e49 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e730 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e591
           grind)
        | exact superpose b2e591 b2e11
        | exact resolve b2e11 b2e591
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e591
      have b2e745 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e730
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e730
        | exact resolve b2e730 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e730
      have b2e845 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e46 x x
           have i₂ := b2e745
           grind)
        | exact superpose b2e745 b2e46
        | exact resolve b2e46 b2e745
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46 b2e745
      have b2e848 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e845
           have r₂ := b2e17
           grind)
        | exact resolve b2e845 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e845
      have b2e920 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e848
           grind)
        | exact superpose b2e848 b2e11
        | exact resolve b2e11 b2e848
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e848
      have b2e939 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e920
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e920
        | exact resolve b2e920 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e920
      have b2e940 : x = y := by grind
      clear b2e939
      have b2e1025 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e940
           grind)
        | exact superpose b2e940 b2e16
        | exact resolve b2e16 b2e940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1029 : x = (M.op x x) := by
        first
        | (have i₁ := b2e54
           have i₂ := b2e940
           grind)
        | exact superpose b2e940 b2e54
        | exact resolve b2e54 b2e940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54
      have b2e1034 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e1025
           have i₂ := b2e1029
           grind)
        | exact superpose b2e1029 b2e1025
        | exact resolve b2e1025 b2e1029
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1025 b2e1029
      have b2e1035 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e1034
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e1034
        | exact resolve b2e1034 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1034
      have b2e1036 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e1035
           have i₂ := b2e940
           grind)
        | exact superpose b2e940 b2e1035
        | exact resolve b2e1035 b2e940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e940 b2e1035
      have b2e1037 : False := by grind
      exact b2e1037
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e32 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 (σ x) X0
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 (σ x) X0
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e112 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e32 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e32
      have b3e113 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e112
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e112
        | exact resolve b3e112 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e112
      have b3e170 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e113
           grind)
        | exact superpose b3e113 b3e16
        | exact resolve b3e16 b3e113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e113
      have b3e221 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e170
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e170
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e170 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e170
      have b3e222 : y = (M.op x x) := by grind
      clear b3e221
      have b3e224 : False := by grind
      exact b3e224

/-- `Equation4295`: `x ◇ (x ◇ y) = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4295 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4295 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4295.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x y) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e19
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e19
        | exact resolve b0e19 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19
      have b0e21 : False := by grind
      exact b0e21
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X0)) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op x y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : y ≠ y ∨ x = (k x y) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 x y
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e21 : x = (k x y) := by grind
      clear b1e20
      have b1e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X1 (M.op X2 X0) X3
           have i₂ := b1e10 X0 X1 X2
           grind)
        | (have i₁ := b1e10 X0 (M.op X0 X1) X2
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e27 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 X0 X3
           have i₂ := b1e10 X2 X0 X1
           grind)
        | (have i₁ := b1e10 X2 X0 X2
           have i₂ := b1e10 X0 X2 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e29 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b1e10 y X0 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X2 X0) X3 X1
           have i₂ := b1e10 X0 X1 X2
           grind)
        | (have i₁ := b1e10 (M.op X0 X1) X1 X0
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e52 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 y X0 X1
           have i₂ := b1e29 X0
           grind)
        | exact superpose b1e29 b1e10
        | exact resolve b1e10 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e53 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 y y
           have i₂ := b1e29 X0
           grind)
        | exact superpose b1e29 b1e10
        | exact resolve b1e10 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e64 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e23 X1 X0
           grind)
        | exact superpose b1e23 b1e11
        | exact resolve b1e11 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23
      have b1e81 : ∀ X0 X1 : G, (M.op X0 y) = (M.op y (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 y X1
           have i₂ := b1e52 X0 X0
           grind)
        | exact superpose b1e52 b1e10
        | exact resolve b1e10 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e131 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op X3 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 X2 X3
           have i₂ := b1e27 X0 X0 X2 X1
           grind)
        | (have i₁ := b1e10 X0 X2 X3
           have i₂ := b1e27 X0 X1 X2 X0
           grind)
        | exact superpose b1e27 b1e10
        | exact resolve b1e10 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e162 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (k X0 (M.op X0 y)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13 X0 (M.op X0 y)
           have i₂ := b1e53 X0
           grind)
        | exact superpose b1e53 b1e13
        | (have j0 := b1e13 X0 (M.op X0 y)
           grind)
        | (have r₁ := b1e13 X0 (M.op X0 y)
           have r₂ := b1e53 X0
           grind)
        | exact resolve b1e13 b1e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53
      have b1e164 : ∀ X0 : G, (k X0 (M.op X0 y)) = X0 := by
        intro X0
        first
        | (have j0 := b1e162 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e162
      have b1e724 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 y) ∨ y = (k y (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 y (M.op X1 X0)
           have i₂ := b1e81 X0 X1
           grind)
        | exact superpose b1e81 b1e13
        | (have j0 := b1e13 y (M.op X1 X0)
           grind)
        | (have r₁ := b1e13 y (M.op y y)
           have r₂ := b1e81 y y
           grind)
        | exact resolve b1e13 b1e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e731 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e27 X1 X2 (M.op X3 X0) y
           have i₂ := b1e81 X0 X3
           grind)
        | exact superpose b1e81 b1e27
        | exact resolve b1e27 b1e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e81
      have b1e740 : ∀ X0 X1 X2 X3 : G, (M.op X1 y) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e731 X0 X1 X2 X3
           have i₂ := b1e52 X1 X0
           grind)
        | exact superpose b1e52 b1e731
        | exact resolve b1e731 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e731
      have b1e967 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) (M.op X4 X0)) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e27 (M.op X3 X1) (M.op X3 X1) X0 X4
           have i₂ := b1e30 X1 X2 X3 X0
           grind)
        | exact superpose b1e30 b1e27
        | exact resolve b1e27 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e998 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X4 (M.op X1 X3))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e27 X2 X1 (M.op X1 X3) X4
           have i₂ := b1e30 X1 X3 X0 X2
           grind)
        | exact superpose b1e30 b1e27
        | exact resolve b1e27 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30
      have b1e1042 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e998 X0 X1 X2 x x
           have i₂ := b1e740 x X2 x X1
           grind)
        | exact superpose b1e740 b1e998
        | exact resolve b1e998 b1e740
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e998
      have b1e1066 : ∀ X0 X1 X3 X4 : G, (M.op X0 y) = (M.op (M.op X3 X1) (M.op X4 X0)) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b1e967 X0 X1 x X3 X4
           have i₂ := b1e740 x X0 X1 X1
           grind)
        | exact superpose b1e740 b1e967
        | exact resolve b1e967 b1e740
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e967
      have b1e1224 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e64 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e64
        | exact resolve b1e64 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e64
      have b1e1251 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (σ X1) (M.op (σ X1) X3))) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e26 (σ X1) X3 (σ X0) X2
           have i₂ := b1e42 X0 X1
           grind)
        | exact superpose b1e42 b1e26
        | (have j1 := b1e42 X0 X1
           grind)
        | exact resolve b1e26 b1e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e1254 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (M.op X3 (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e27 X2 X3 (σ X1) (σ X0)
           have i₂ := b1e42 X0 X1
           grind)
        | exact superpose b1e42 b1e27
        | (have j1 := b1e42 X0 X1
           grind)
        | exact resolve b1e27 b1e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27
      have b1e1264 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e42 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42
      have b1e1268 : ∀ X0 X1 X2 X3 : G, (M.op X3 y) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e1251 X0 X1 X2 X3
           have i₂ := b1e740 X3 X3 (σ X1) (σ X1)
           grind)
        | exact superpose b1e740 b1e1251
        | (have j0 := b1e1251 X0 X1 X2 X3
           grind)
        | exact resolve b1e1251 b1e740
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1251
      have b1e1280 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) y))) := by
        intro X0
        first
        | (have i₁ := b1e75 X0 (M.op (σ X0) y)
           have i₂ := b1e164 (σ X0)
           grind)
        | exact superpose b1e164 b1e75
        | exact resolve b1e75 b1e164
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e75 b1e164
      have b1e1292 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) y))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e1280 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e1280
        | exact resolve b1e1280 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1280
      have b1e48975 : ∀ X0 X1 X2 X3 : G, (M.op X2 y) = (M.op (σ (τ (k X0 X1))) (M.op X3 X2)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e1268 (τ X0) (τ X1) X3 X2
           have i₂ := b1e1224 X1 X0
           grind)
        | exact superpose b1e1224 b1e1268
        | (have j0 := b1e1268 (τ X0) (τ X1) X2 X3
           grind)
        | exact resolve b1e1268 b1e1224
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1224
      have b1e48978 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (σ x) (M.op X1 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e1268 x y X1 X0
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e1268
        | (have j0 := b1e1268 x y x x
           grind)
        | exact resolve b1e1268 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1268
      have b1e49672 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (σ x) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e48978 X0 X1
           grind)
        | (have r₁ := b1e48978 X0 X1
           have r₂ := b1e18
           grind)
        | exact resolve b1e48978 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48978
      have b1e49673 : ∀ X0 X1 X2 X3 : G, (M.op X2 y) = (M.op (k X0 X1) (M.op X3 X2)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e48975 X0 X1 X2 X3
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e48975
        | (have j0 := b1e48975 X0 X1 X2 X3
           grind)
        | exact resolve b1e48975 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48975
      have b1e49874 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X2 y) = (M.op (k X0 X1) (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e49673 X0 X0 X2 X3
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e49673
        | (have j0 := b1e49673 X0 X1 X2 X3
           grind)
        | exact resolve b1e49673 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49673
      have b1e49912 : ∀ X0 X1 X2 X3 : G, (M.op X2 y) = (M.op (k X0 X1) (M.op X3 X2)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e49874 X0 X1 X2 X3
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e49874
        | (have j0 := b1e49874 X0 X1 X2 X3
           grind)
        | exact resolve b1e49874 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49874
      have b1e50159 : (M.op y y) = (M.op (σ x) y) := by
        first
        | (have i₁ := b1e52 (σ x) x
           have i₂ := b1e49672 y x
           grind)
        | exact superpose b1e49672 b1e52
        | exact resolve b1e52 b1e49672
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e53687 : x = (k x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e1292 x
           have i₂ := b1e50159
           grind)
        | exact superpose b1e50159 b1e1292
        | exact resolve b1e1292 b1e50159
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1292 b1e50159
      have b1e83222 : ∀ X0 X1 : G, (M.op y y) = (M.op (k X0 X1) y) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e52 (k X0 X1) x
           have i₂ := b1e49912 X0 X1 y x
           grind)
        | exact superpose b1e49912 b1e52
        | (have j1 := b1e49912 X0 X1 x x
           grind)
        | exact resolve b1e52 b1e49912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e52 b1e49912
      have b1e87550 : (M.op x y) = (M.op y y) ∨ (τ (M.op y y)) = (M.op x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e83222 x (τ (M.op y y))
           have i₂ := b1e53687
           grind)
        | exact superpose b1e53687 b1e83222
        | (have j0 := b1e83222 x (τ (M.op y y))
           grind)
        | exact resolve b1e83222 b1e53687
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53687 b1e83222
      have b1e87736 : (τ (M.op y y)) = (M.op x (τ (M.op y y))) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e87550
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e87550
        | exact resolve b1e87550 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e87550
      have b1e95151 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e1254 x y X0 X1
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e1254
        | (have j0 := b1e1254 x y x x
           grind)
        | exact resolve b1e1254 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e1254
      have b1e96101 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ y))) := by
        intro X0 X1
        first
        | (have j0 := b1e95151 X0 X1
           grind)
        | (have r₁ := b1e95151 X0 X1
           have r₂ := b1e18
           grind)
        | exact resolve b1e95151 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e95151
      have b1e96405 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (σ y) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e131 (σ y) X1 X0 x
           have i₂ := b1e96101 X0 x
           grind)
        | exact superpose b1e96101 b1e131
        | exact resolve b1e131 b1e96101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e96631 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (σ y) y) := by
        intro X0 X1
        first
        | (have i₁ := b1e1042 X0 X1 (σ y)
           have i₂ := b1e96101 (M.op X0 X1) (M.op X0 X1)
           grind)
        | exact superpose b1e96101 b1e1042
        | exact resolve b1e1042 b1e96101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1042
      have b1e96664 : (M.op y (σ x)) = (M.op (σ y) y) := by
        first
        | (have i₁ := b1e29 (σ y)
           have i₂ := b1e96101 y y
           grind)
        | exact superpose b1e96101 b1e29
        | exact resolve b1e29 b1e96101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29
      have b1e96695 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op y (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b1e96631 X0 X1
           have i₂ := b1e96664
           grind)
        | exact superpose b1e96664 b1e96631
        | exact resolve b1e96631 b1e96664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96631 b1e96664
      have b1e193121 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 (τ (M.op y y)))) ∨ y = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b1e740 (τ (M.op y y)) X0 X1 x
           have i₂ := b1e87736
           grind)
        | exact superpose b1e87736 b1e740
        | exact resolve b1e740 b1e87736
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e740
      have b1e326876 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (M.op y y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b1e193121 X0 x
           have i₂ := b1e87736
           grind)
        | exact superpose b1e87736 b1e193121
        | exact resolve b1e193121 b1e87736
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e193121
      have b1e327472 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (M.op y y))) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have j0 := b1e326876 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e326876
      have b1e336238 : (M.op x y) = (τ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e87736
           have i₂ := b1e327472 x
           grind)
        | exact superpose b1e327472 b1e87736
        | exact resolve b1e87736 b1e327472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e87736 b1e327472
      have b1e336245 : (M.op x y) = (τ (M.op y y)) ∨ y = (M.op y y) := by grind
      clear b1e336238
      have b1e336250 : y = (τ (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e336245
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e336245
        | exact resolve b1e336245 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e336245
      have b1e344476 : (σ y) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e12 (M.op y y)
           have i₂ := b1e336250
           grind)
        | exact superpose b1e336250 b1e12
        | exact resolve b1e12 b1e336250
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e336250
      have b1e355307 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e49672 y y
           have i₂ := b1e344476
           grind)
        | exact superpose b1e344476 b1e49672
        | exact resolve b1e49672 b1e344476
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e344476
      have b1e355325 : y = (M.op y y) := by
        first
        | (have r₁ := b1e355307
           have r₂ := b1e18
           grind)
        | exact resolve b1e355307 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e355307
      have b1e358955 : y ≠ y ∨ y = (k y y) := by
        first
        | (have i₁ := b1e724 y y
           have i₂ := b1e355325
           grind)
        | exact superpose b1e355325 b1e724
        | exact resolve b1e724 b1e355325
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e724
      have b1e358980 : y = (M.op (σ x) y) := by
        first
        | (have i₁ := b1e49672 y y
           have i₂ := b1e355325
           grind)
        | exact superpose b1e355325 b1e49672
        | exact resolve b1e49672 b1e355325
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49672
      have b1e358990 : y = (k y y) := by grind
      clear b1e358955
      have b1e363098 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e1264 y y
           have i₂ := b1e358990
           grind)
        | exact superpose b1e358990 b1e1264
        | (have j0 := b1e1264 y y
           grind)
        | exact resolve b1e1264 b1e358990
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1264 b1e358990
      have b1e363123 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b1e363098
      have b1e382090 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e96101 X0 (σ y)
           have i₂ := b1e363123
           grind)
        | exact superpose b1e363123 b1e96101
        | exact resolve b1e96101 b1e363123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96101
      have b1e382125 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (σ y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e131 (σ y) X0 X1 (σ y)
           have i₂ := b1e363123
           grind)
        | exact superpose b1e363123 b1e131
        | exact resolve b1e131 b1e363123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e131
      have b1e382347 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (σ y) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e1066 X0 (σ y) (σ y) X1
           have i₂ := b1e363123
           grind)
        | exact superpose b1e363123 b1e1066
        | exact resolve b1e1066 b1e363123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1066
      have b1e382357 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e96405 (σ y) (σ y)
           have i₂ := b1e363123
           grind)
        | exact superpose b1e363123 b1e96405
        | exact resolve b1e96405 b1e363123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96405
      have b1e382359 : (M.op y (σ x)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e96695 (σ y) (σ y)
           have i₂ := b1e363123
           grind)
        | exact superpose b1e363123 b1e96695
        | exact resolve b1e96695 b1e363123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96695
      have b1e382365 : (M.op y (σ x)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e382357
           have i₂ := b1e382359
           grind)
        | exact superpose b1e382359 b1e382357
        | exact resolve b1e382357 b1e382359
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e382357 b1e382359
      have b1e382542 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (σ y)) := by
        intro X1
        first
        | (have i₁ := b1e382125 x X1
           have i₂ := b1e382347 X1 x
           grind)
        | exact superpose b1e382347 b1e382125
        | exact resolve b1e382125 b1e382347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e382125 b1e382347
      have b1e382574 : (σ y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e382365
           have i₂ := b1e363123
           grind)
        | exact superpose b1e363123 b1e382365
        | exact resolve b1e382365 b1e363123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e363123 b1e382365
      have b1e382684 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e382574
           have i₂ := b1e382090 y
           grind)
        | exact superpose b1e382090 b1e382574
        | exact resolve b1e382574 b1e382090
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e382090 b1e382574
      have b1e382789 : (σ y) = (M.op y y) := by
        first
        | (have i₁ := b1e382684
           have i₂ := b1e382542 y
           grind)
        | exact superpose b1e382542 b1e382684
        | exact resolve b1e382684 b1e382542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e382542 b1e382684
      have b1e382878 : y = (σ y) := by
        first
        | (have i₁ := b1e382789
           have i₂ := b1e355325
           grind)
        | exact superpose b1e355325 b1e382789
        | exact resolve b1e382789 b1e355325
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e355325 b1e382789
      have b1e383291 : y ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e382878
           grind)
        | exact superpose b1e382878 b1e18
        | exact resolve b1e18 b1e382878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e382878
      have b1e383372 : False := by grind
      exact b1e383372
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X0)) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op x y) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 (σ x) (σ y)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e21 : (σ x) = (k (σ x) (σ y)) := by grind
      clear b2e20
      have b2e22 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e21
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e21
        | exact resolve b2e21 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e23 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e22
           grind)
        | exact superpose b2e22 b2e11
        | exact resolve b2e11 b2e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22
      have b2e24 : x = (k x y) := by
        first
        | (have i₁ := b2e23
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e23
        | exact resolve b2e23 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23
      have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e31 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) (σ y) X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X2)) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 (M.op X2 X0) X3
           have i₂ := b2e10 X2 X0 X1
           grind)
        | (have i₁ := b2e10 X1 (M.op X2 X0) X2
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X1 (M.op X2 X0) X3
           have i₂ := b2e10 X0 X1 X2
           grind)
        | (have i₁ := b2e10 X0 (M.op X0 X1) X2
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 X0 X3
           have i₂ := b2e10 X2 X0 X1
           grind)
        | (have i₁ := b2e10 X2 X0 X2
           have i₂ := b2e10 X0 X2 X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e36 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ y) X0 (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 (M.op X2 X0) X3 X1
           have i₂ := b2e10 X0 X1 X2
           grind)
        | (have i₁ := b2e10 (M.op X0 X1) X1 X0
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X0 X2 X2
           have i₂ := b2e10 X2 X0 X1
           grind)
        | (have i₁ := b2e10 X0 X1 X2
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e39 : ∀ X0 X1 X2 : G, (M.op X2 X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (k X2 (M.op X2 X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X2 (M.op X2 X0)
           have i₂ := b2e10 X2 X0 X1
           grind)
        | (have i₁ := b2e13 X1 (M.op X2 X0)
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e13
        | (have j0 := b2e13 X2 (M.op X2 X0)
           grind)
        | exact resolve b2e13 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e41 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) := by
        intro X0
        first
        | (have i₁ := b2e31 X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e31
        | exact resolve b2e31 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e45 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k (τ X0) X1)
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e11
        | exact resolve b2e11 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e14 (σ X0) (σ X1)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X0) (σ X1)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e50 : x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e24
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e24
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e24 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e53 : x = (M.op x y) := by
        first
        | (have r₁ := b2e50
           have r₂ := b2e17
           grind)
        | exact resolve b2e50 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50
      have b2e56 : x ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e17
        | exact resolve b2e17 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e57 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b2e10 y X0 x
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e10
        | exact resolve b2e10 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e58 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e10 x y X0
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e10
        | exact resolve b2e10 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e66 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e27 X1 X0
           grind)
        | exact superpose b2e27 b2e11
        | exact resolve b2e11 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e71 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (σ y))) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ y) (σ x) X0
           have i₂ := b2e41 (σ y)
           grind)
        | exact superpose b2e41 b2e10
        | exact resolve b2e10 b2e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e88 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 X0 X1 (σ y) (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e34
        | exact resolve b2e34 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e89 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (M.op X2 (σ x)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e34 X0 X1 (M.op X2 (σ x)) (σ y)
           have i₂ := b2e41 X2
           grind)
        | exact superpose b2e41 b2e34
        | exact resolve b2e34 b2e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e94 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 X0 X1 y x
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e34
        | exact resolve b2e34 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e107 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op X3 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X0 X2 X3
           have i₂ := b2e34 X0 X0 X2 X1
           grind)
        | (have i₁ := b2e10 X0 X2 X3
           have i₂ := b2e34 X0 X1 X2 X0
           grind)
        | exact superpose b2e34 b2e10
        | exact resolve b2e10 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e168 : ∀ X0 X1 : G, (M.op y (M.op y (M.op y X0))) = (M.op (M.op X1 X0) x) := by
        intro X0 X1
        first
        | (have i₁ := b2e57 (M.op X1 X0)
           have i₂ := b2e38 y X1 X0
           grind)
        | (have i₁ := b2e57 (M.op y x)
           have i₂ := b2e38 y X1 x
           grind)
        | exact superpose b2e38 b2e57
        | exact resolve b2e57 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e180 : ∀ X0 X1 : G, (M.op X0 x) = (M.op y (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 y y X0 X1
           have i₂ := b2e57 X0
           grind)
        | exact superpose b2e57 b2e34
        | exact resolve b2e34 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e184 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op y X0))) = (M.op X1 (M.op X0 x)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e34 X1 X2 (M.op y X0) y
           have i₂ := b2e57 X0
           grind)
        | exact superpose b2e57 b2e34
        | exact resolve b2e34 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57
      have b2e191 : ∀ X0 X1 : G, (M.op y (M.op X0 x)) = (M.op (M.op X1 X0) x) := by
        intro X0 X1
        first
        | (have i₁ := b2e168 X0 X1
           have i₂ := b2e184 X0 y y
           grind)
        | exact superpose b2e184 b2e168
        | exact resolve b2e168 b2e184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168 b2e184
      have b2e196 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X1 X0) x) := by
        intro X0 X1
        first
        | (have i₁ := b2e191 X0 X1
           have i₂ := b2e58 X0
           grind)
        | exact superpose b2e58 b2e191
        | exact resolve b2e191 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58 b2e191
      have b2e197 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e36 (M.op X0 (σ x))
           have i₂ := b2e41 X0
           grind)
        | exact superpose b2e41 b2e36
        | exact resolve b2e36 b2e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e215 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 (σ y) (σ y) X0 X1
           have i₂ := b2e36 X0
           grind)
        | exact superpose b2e36 b2e34
        | exact resolve b2e34 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e312 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e32 (σ y) (σ y) X0 X1
           have i₂ := b2e36 X0
           grind)
        | exact superpose b2e36 b2e32
        | exact resolve b2e32 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e337 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X3 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X0 (M.op X2 X0) X3
           have i₂ := b2e32 X0 X2 X0 X1
           grind)
        | exact superpose b2e32 b2e10
        | exact resolve b2e10 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32
      have b2e363 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e312 X0 X1
           have i₂ := b2e88 X0 X0
           grind)
        | exact superpose b2e88 b2e312
        | exact resolve b2e312 b2e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e312
      have b2e450 : (M.op y (σ y)) = (M.op (σ y) x) := by
        first
        | (have i₁ := b2e36 y
           have i₂ := b2e94 (σ y) (σ y)
           grind)
        | exact superpose b2e94 b2e36
        | exact resolve b2e36 b2e94
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e503 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ x)) (M.op X1 (M.op X1 (M.op X2 (σ x))))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e33 X1 (M.op X2 (σ x)) X0 (σ y)
           have i₂ := b2e41 X2
           grind)
        | exact superpose b2e41 b2e33
        | exact resolve b2e33 b2e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e543 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op X1 (σ y)) (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e33 (σ y) X0 X1 X2
           have i₂ := b2e36 X0
           grind)
        | exact superpose b2e36 b2e33
        | exact resolve b2e33 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e600 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op X1 (σ y)) (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e543 X0 X1 X2
           have i₂ := b2e88 X0 X0
           grind)
        | exact superpose b2e88 b2e543
        | exact resolve b2e543 b2e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e543
      have b2e614 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ x)) (M.op X1 (σ y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e503 X0 X1 X2
           have i₂ := b2e89 X1 X1 X2
           grind)
        | exact superpose b2e89 b2e503
        | exact resolve b2e503 b2e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e89 b2e503
      have b2e633 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ x)) (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e614 X0 X1 X2
           have i₂ := b2e88 (M.op X2 (σ x)) X1
           grind)
        | exact superpose b2e88 b2e614
        | exact resolve b2e614 b2e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e614
      have b2e644 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e633 X0 X1 x
           have i₂ := b2e197 x
           grind)
        | exact superpose b2e197 b2e633
        | exact resolve b2e633 b2e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197 b2e633
      have b2e675 : ∀ X0 : G, (M.op y (σ y)) = (M.op (M.op X0 (σ x)) x) := by
        intro X0
        first
        | (have i₁ := b2e180 (M.op X0 (σ x)) (σ y)
           have i₂ := b2e41 X0
           grind)
        | exact superpose b2e41 b2e180
        | exact resolve b2e180 b2e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e41
      have b2e706 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X3 X0))) = (M.op X1 (M.op X0 x)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e34 X1 X2 (M.op X3 X0) y
           have i₂ := b2e180 X0 X3
           grind)
        | exact superpose b2e180 b2e34
        | exact resolve b2e34 b2e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34 b2e180
      have b2e724 : (M.op x x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b2e675 x
           have i₂ := b2e196 (σ x) x
           grind)
        | exact superpose b2e196 b2e675
        | exact resolve b2e675 b2e196
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e196 b2e675
      have b2e803 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (M.op X0 (σ y)) ∨ (k X0 (M.op X0 (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e39 (σ y) (σ y) X0
           have i₂ := b2e36 X0
           grind)
        | exact superpose b2e36 b2e39
        | (have j0 := b2e39 (σ y) x X0
           grind)
        | (have r₁ := b2e39 (σ y) (σ y) X0
           have r₂ := b2e36 X0
           grind)
        | exact resolve b2e39 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e39
      have b2e807 : ∀ X0 : G, (k X0 (M.op X0 (σ y))) = X0 := by
        intro X0
        first
        | (have j0 := b2e803 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e803
      have b2e950 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ y) X0) (M.op (M.op (σ y) X0) X2))) = (M.op (M.op X0 (σ y)) (M.op (M.op X0 (σ y)) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e37 (M.op (σ y) X0) X1 (σ y) x
           have i₂ := b2e36 X0
           grind)
        | exact superpose b2e36 b2e37
        | exact resolve b2e37 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e37
      have b2e1180 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op (M.op (σ y) X0) (M.op (M.op (σ y) X0) X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e950 X0 X1 X2
           have i₂ := b2e600 X1 X0 (M.op X0 (σ y))
           grind)
        | exact superpose b2e600 b2e950
        | exact resolve b2e950 b2e600
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e600 b2e950
      have b2e1256 : ∀ X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X2 x)) := by
        intro X1 X2
        first
        | (have i₁ := b2e1180 x X1 X2
           have i₂ := b2e706 X2 X1 (M.op (σ y) x) (M.op (σ y) x)
           grind)
        | exact superpose b2e706 b2e1180
        | exact resolve b2e1180 b2e706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1180
      have b2e1429 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e48 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1482 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e45 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e45
        | exact resolve b2e45 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1487 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e45 X0 X1
           have i₂ := b2e14 X0 (σ X1)
           grind)
        | exact superpose b2e14 b2e45
        | (have j1 := b2e14 X0 (σ X1)
           grind)
        | exact resolve b2e45 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45
      have b2e1545 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e66 X0 X1
           have i₂ := b2e14 (σ X0) X1
           grind)
        | exact superpose b2e14 b2e66
        | (have j1 := b2e14 (σ X0) X1
           grind)
        | exact resolve b2e66 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1546 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ y)))) := by
        intro X0
        first
        | (have i₁ := b2e66 X0 (M.op (σ X0) (σ y))
           have i₂ := b2e807 (σ X0)
           grind)
        | exact superpose b2e807 b2e66
        | exact resolve b2e66 b2e807
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e66
      have b2e1554 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ y)))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e1546 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e1546
        | exact resolve b2e1546 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1546
      have b2e1604 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ y)) (M.op X1 (M.op X1 (M.op X2 (σ y))))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e33 X1 (M.op X2 (σ y)) X0 (σ x)
           have i₂ := b2e71 X2
           grind)
        | exact superpose b2e71 b2e33
        | exact resolve b2e33 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33
      have b2e1623 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ y)) (M.op (M.op X2 (σ y)) x)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e1604 X0 X1 X2
           have i₂ := b2e706 (M.op X2 (σ y)) (M.op X2 (σ y)) X1 X1
           grind)
        | exact superpose b2e706 b2e1604
        | exact resolve b2e1604 b2e706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1604
      have b2e1631 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op x (M.op x (M.op X2 (σ y)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e1623 X0 X1 X2
           have i₂ := b2e10 x (M.op X2 (σ y)) (M.op X2 (σ y))
           grind)
        | (have i₁ := b2e1623 X0 X1 X2
           have i₂ := b2e10 (M.op X2 (σ y)) x X2
           grind)
        | exact superpose b2e10 b2e1623
        | exact resolve b2e1623 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1623
      have b2e1637 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op x (M.op (σ y) x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1631 X0 X1 x
           have i₂ := b2e706 (σ y) x x x
           grind)
        | exact superpose b2e706 b2e1631
        | exact resolve b2e1631 b2e706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1631
      have b2e1641 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op x (M.op x x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1637 X0 X1
           have i₂ := b2e10 x x (σ y)
           grind)
        | exact superpose b2e10 b2e1637
        | exact resolve b2e1637 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1637
      have b2e1645 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op x (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1641 X0 X1
           have i₂ := b2e1256 x x
           grind)
        | exact superpose b2e1256 b2e1641
        | exact resolve b2e1641 b2e1256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1641
      have b2e1652 : (M.op x (σ y)) = (M.op (σ y) (M.op y (σ y))) := by
        first
        | (have i₁ := b2e36 x
           have i₂ := b2e450
           grind)
        | exact superpose b2e450 b2e36
        | exact resolve b2e36 b2e450
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e36 b2e450
      have b2e1690 : (M.op (σ y) (σ y)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e1652
           have i₂ := b2e215 (σ y) y
           grind)
        | exact superpose b2e215 b2e1652
        | exact resolve b2e1652 b2e215
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1652
      have b2e2183 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X3 (M.op X4 X0))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e38 X3 X2 (M.op X4 X0)
           have i₂ := b2e107 X2 X4 X0 X1
           grind)
        | (have i₁ := b2e38 X3 X2 (M.op X4 X0)
           have i₂ := b2e107 X0 X1 X2 X4
           grind)
        | exact superpose b2e107 b2e38
        | exact resolve b2e38 b2e107
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e38
      have b2e2210 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X0 x)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e2183 X0 X1 X2 X3 x
           have i₂ := b2e706 X0 X3 X3 x
           grind)
        | exact superpose b2e706 b2e2183
        | exact resolve b2e2183 b2e706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e706 b2e2183
      have b2e2271 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (σ y)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e2210 X0 X1 X2 X3
           have i₂ := b2e1256 X3 X0
           grind)
        | exact superpose b2e1256 b2e2210
        | exact resolve b2e2210 b2e1256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1256 b2e2210
      have b2e2399 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (σ y))) = (M.op (M.op X1 X0) (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e107 (M.op X1 X0) X2 X3 (σ y)
           have i₂ := b2e215 X0 X1
           grind)
        | exact superpose b2e215 b2e107
        | exact resolve b2e107 b2e215
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e107 b2e215
      have b2e2404 : ∀ X0 X1 X2 X3 : G, (M.op X3 (σ y)) = (M.op (M.op X1 X0) (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e2399 X0 X1 X2 X3
           have i₂ := b2e88 X3 X0
           grind)
        | exact superpose b2e88 b2e2399
        | exact resolve b2e2399 b2e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2399
      have b2e2833 : ∀ X0 X1 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 X1) = (k (M.op X0 X1) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 (M.op X0 X1) (σ y)
           have i₂ := b2e644 X0 X1
           grind)
        | exact superpose b2e644 b2e13
        | (have j0 := b2e13 (σ y) (σ y)
           grind)
        | exact resolve b2e13 b2e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e644
      have b2e2854 : ∀ X0 X1 : G, (σ y) ≠ (M.op x (σ y)) ∨ (M.op X0 X1) = (k (M.op X0 X1) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e2833 X0 X1
           have i₂ := b2e1690
           grind)
        | exact superpose b2e1690 b2e2833
        | (have j0 := b2e2833 X0 X1
           grind)
        | exact resolve b2e2833 b2e1690
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2833
      have b2e4335 : ∀ X0 X1 : G, (σ (k X0 y)) = (M.op (σ (k X0 y)) (M.op X1 (σ X0))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e363 (σ X0) X1
           have i₂ := b2e48 X0 y
           grind)
        | exact superpose b2e48 b2e363
        | (have j1 := b2e48 X0 y
           grind)
        | exact resolve b2e363 b2e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48 b2e363
      have b2e30793 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e1429 (τ X0) (τ X1)
           have i₂ := b2e1482 X1 X0
           grind)
        | exact superpose b2e1482 b2e1429
        | (have j0 := b2e1429 (τ X0) (τ X1)
           grind)
        | exact resolve b2e1429 b2e1482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1429
      have b2e30805 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e30793 X0 X1
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e30793
        | (have j0 := b2e30793 X0 X1
           grind)
        | exact resolve b2e30793 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30793
      have b2e30810 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e30805 X0 X1
           have i₂ := b2e12 X1
           grind)
        | exact superpose b2e12 b2e30805
        | (have j0 := b2e30805 X0 X1
           grind)
        | exact resolve b2e30805 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30805
      have b2e30814 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e30810 X0 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e30810
        | (have j0 := b2e30810 X0 X1
           grind)
        | exact resolve b2e30810 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30810
      have b2e30815 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e30814 X0 X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e30814
        | (have j0 := b2e30814 X0 X1
           grind)
        | exact resolve b2e30814 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30814
      have b2e30827 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e30815 (τ X0) (τ X1)
           have i₂ := b2e1482 X1 X0
           grind)
        | exact superpose b2e1482 b2e30815
        | (have j0 := b2e30815 (τ X0) (τ X1)
           grind)
        | exact resolve b2e30815 b2e1482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1482
      have b2e138938 : (τ (M.op x (σ y))) = (k y (τ (σ y))) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e1545 y (σ y)
           have i₂ := b2e1690
           grind)
        | exact superpose b2e1690 b2e1545
        | exact resolve b2e1545 b2e1690
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e138943 : ∀ X0 : G, (τ (σ y)) = (k x (τ (M.op X0 (σ y)))) ∨ (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e1545 x (M.op X0 (σ y))
           have i₂ := b2e71 X0
           grind)
        | exact superpose b2e71 b2e1545
        | exact resolve b2e1545 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e71 b2e1545
      have b2e139080 : ∀ X0 : G, y = (k x (τ (M.op X0 (σ y)))) ∨ (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e138943 X0
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e138943
        | (have j0 := b2e138943 X0
           grind)
        | exact resolve b2e138943 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e138943
      have b2e139083 : (k y y) = (τ (M.op x (σ y))) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e138938
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e138938
        | exact resolve b2e138938 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e138938
      have b2e298340 : y = (k x (k y y)) ∨ (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e139080 x
           have i₂ := b2e139083
           grind)
        | exact superpose b2e139083 b2e139080
        | (have j0 := b2e139080 x
           grind)
        | exact resolve b2e139080 b2e139083
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e139080 b2e139083
      have b2e298352 : y = (k x (k y y)) ∨ (σ y) = (M.op x (σ y)) := by grind
      clear b2e298340
      have b2e341151 : ∀ X0 X1 : G, (τ (M.op x (σ y))) = (k (τ (M.op X0 X1)) y) ∨ (σ y) = (M.op x (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1487 (M.op X0 X1) y
           have i₂ := b2e1645 X0 X1
           grind)
        | exact superpose b2e1645 b2e1487
        | (have j0 := b2e1487 x y
           grind)
        | exact resolve b2e1487 b2e1645
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1487
      have b2e691456 : (σ (k y y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e88 (σ (k y y)) x
           have i₂ := b2e4335 y x
           grind)
        | exact superpose b2e4335 b2e88
        | (have j1 := b2e4335 y x
           grind)
        | exact resolve b2e88 b2e4335
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e88 b2e4335
      have b2e692010 : (σ (k y y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e691456
           have i₂ := b2e1690
           grind)
        | exact superpose b2e1690 b2e691456
        | exact resolve b2e691456 b2e1690
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e691456
      have b2e698842 : ∀ X0 X1 : G, (k (M.op X0 X1) (σ y)) = (σ (τ (M.op x (σ y)))) ∨ (σ y) = (M.op x (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e25 (M.op X0 X1) y
           have i₂ := b2e341151 X0 X1
           grind)
        | exact superpose b2e341151 b2e25
        | exact resolve b2e25 b2e341151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25 b2e341151
      have b2e698852 : ∀ X0 X1 : G, (M.op x (σ y)) = (k (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e698842 X0 X1
           have i₂ := b2e12 (M.op x (σ y))
           grind)
        | exact superpose b2e12 b2e698842
        | exact resolve b2e698842 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e698842
      have b2e700779 : (M.op x (σ y)) = (k (M.op x (σ y)) (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e698852 (σ y) (σ y)
           have i₂ := b2e1690
           grind)
        | exact superpose b2e1690 b2e698852
        | (have j0 := b2e698852 x (σ y)
           grind)
        | exact resolve b2e698852 b2e1690
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1690 b2e698852
      have b2e700846 : (M.op x (σ y)) = (k (M.op x (σ y)) (σ y)) := by
        first
        | (have j1 := b2e2854 x (σ y)
           grind)
        | (have r₁ := b2e700779
           have r₂ := b2e2854 x x
           grind)
        | exact resolve b2e700779 b2e2854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2854 b2e700779
      have b2e701356 : (τ (σ y)) ≠ (τ (M.op x (σ y))) ∨ (τ (σ y)) = (M.op (τ (M.op x (σ y))) (τ (σ y))) := by
        first
        | (have i₁ := b2e30827 (M.op x (σ y)) (σ y)
           have i₂ := b2e700846
           grind)
        | exact superpose b2e700846 b2e30827
        | (have j0 := b2e30827 (M.op x (σ y)) (σ y)
           grind)
        | exact resolve b2e30827 b2e700846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30827 b2e700846
      have b2e701395 : y ≠ (τ (M.op x (σ y))) ∨ (τ (σ y)) = (M.op (τ (M.op x (σ y))) (τ (σ y))) := by
        first
        | (have i₁ := b2e701356
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e701356
        | exact resolve b2e701356 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e701356
      have b2e701404 : y ≠ (τ (M.op x (σ y))) ∨ y = (M.op (τ (M.op x (σ y))) y) := by
        first
        | (have i₁ := b2e701395
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e701395
        | exact resolve b2e701395 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e701395
      have b2e708900 : (k y y) = (k (k y y) (τ (σ (k y y)))) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e1554 (k y y)
           have i₂ := b2e692010
           grind)
        | exact superpose b2e692010 b2e1554
        | exact resolve b2e1554 b2e692010
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1554 b2e692010
      have b2e709090 : (k y y) = (k (k y y) (k y y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e708900
           have i₂ := b2e11 (k y y)
           grind)
        | exact superpose b2e11 b2e708900
        | exact resolve b2e708900 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e708900
      have b2e709684 : (k y y) ≠ (k y y) ∨ (k y y) = (M.op (k y y) (k y y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e30815 (k y y) (k y y)
           have i₂ := b2e709090
           grind)
        | exact superpose b2e709090 b2e30815
        | (have j0 := b2e30815 (k y y) (k y y)
           grind)
        | (have r₁ := b2e30815 (k y y) (k y y)
           have r₂ := b2e709090
           grind)
        | exact resolve b2e30815 b2e709090
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30815 b2e709090
      have b2e709685 : (k y y) = (M.op (k y y) (k y y)) ∨ (σ y) = (M.op x (σ y)) := by grind
      clear b2e709684
      have b2e711987 : (M.op x (σ y)) = (M.op (k y y) (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e1645 (k y y) (k y y)
           have i₂ := b2e709685
           grind)
        | exact superpose b2e709685 b2e1645
        | exact resolve b2e1645 b2e709685
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1645
      have b2e712003 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (k y y))) ∨ (σ y) = (M.op x (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e2271 X1 (k y y) (k y y) X0
           have i₂ := b2e709685
           grind)
        | exact superpose b2e709685 b2e2271
        | exact resolve b2e2271 b2e709685
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2271
      have b2e749006 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k y y)) ∨ (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e712003 X0 (k y y)
           have i₂ := b2e709685
           grind)
        | exact superpose b2e709685 b2e712003
        | exact resolve b2e712003 b2e709685
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e712003
      have b2e749202 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k y y)) ∨ (σ y) = (M.op x (σ y)) := by
        intro X0
        first
        | (have j0 := b2e749006 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e749006
      have b2e750990 : (k y y) = (M.op (k y y) (σ y)) ∨ (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e709685
           have i₂ := b2e749202 (k y y)
           grind)
        | exact superpose b2e749202 b2e709685
        | exact resolve b2e709685 b2e749202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e709685 b2e749202
      have b2e751004 : (k y y) = (M.op (k y y) (σ y)) ∨ (σ y) = (M.op x (σ y)) := by grind
      clear b2e750990
      have b2e752112 : (M.op x (σ y)) = (k y y) ∨ (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e711987
           have i₂ := b2e751004
           grind)
        | exact superpose b2e751004 b2e711987
        | exact resolve b2e711987 b2e751004
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e711987 b2e751004
      have b2e752235 : (M.op x (σ y)) = (k y y) ∨ (σ y) = (M.op x (σ y)) := by grind
      clear b2e752112
      have b2e753030 : x = (k x (k y y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e807 x
           have i₂ := b2e752235
           grind)
        | exact superpose b2e752235 b2e807
        | exact resolve b2e807 b2e752235
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e807 b2e752235
      have b2e755319 : x = y ∨ (σ y) = (M.op x (σ y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e298352
           have i₂ := b2e753030
           grind)
        | exact superpose b2e753030 b2e298352
        | exact resolve b2e298352 b2e753030
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e298352 b2e753030
      have b2e755335 : x = y ∨ (σ y) = (M.op x (σ y)) := by grind
      clear b2e755319
      have b2e755343 : (σ y) = (M.op x (σ y)) := by
        first
        | (have r₁ := b2e755335
           have r₂ := b2e56
           grind)
        | exact resolve b2e755335 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e755335
      have b2e756582 : y ≠ (τ (σ y)) ∨ y = (M.op (τ (σ y)) y) := by
        first
        | (have i₁ := b2e701404
           have i₂ := b2e755343
           grind)
        | exact superpose b2e755343 b2e701404
        | exact resolve b2e701404 b2e755343
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e701404 b2e755343
      have b2e757019 : y = (M.op (τ (σ y)) y) := by
        first
        | (have r₁ := b2e756582
           have r₂ := b2e11 y
           grind)
        | exact resolve b2e756582 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e756582
      have b2e757110 : y = (M.op y y) := by
        first
        | (have i₁ := b2e757019
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e757019
        | exact resolve b2e757019 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e757019
      have b2e758048 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b2e94 X0 y
           have i₂ := b2e757110
           grind)
        | exact superpose b2e757110 b2e94
        | exact resolve b2e94 b2e757110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e758139 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op (M.op X1 y) y) := by
        intro X0 X1
        first
        | (have i₁ := b2e337 y X1 x y
           have i₂ := b2e757110
           grind)
        | exact superpose b2e757110 b2e337
        | exact resolve b2e337 b2e757110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e337
      have b2e758329 : ∀ X0 X1 : G, (M.op y (σ y)) = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b2e2404 X1 X0 y y
           have i₂ := b2e757110
           grind)
        | exact superpose b2e757110 b2e2404
        | exact resolve b2e2404 b2e757110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2404
      have b2e758355 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b2e758329 X0 X1
           have i₂ := b2e724
           grind)
        | exact superpose b2e724 b2e758329
        | exact resolve b2e758329 b2e724
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e724 b2e758329
      have b2e758501 : ∀ X1 : G, (M.op y x) = (M.op (M.op X1 y) y) := by
        intro X1
        first
        | (have i₁ := b2e758139 x X1
           have i₂ := b2e94 y x
           grind)
        | exact superpose b2e94 b2e758139
        | exact resolve b2e758139 b2e94
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e94 b2e758139
      have b2e758561 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b2e758355 X0 X1
           have i₂ := b2e758048 x
           grind)
        | exact superpose b2e758048 b2e758355
        | exact resolve b2e758355 b2e758048
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e758355
      have b2e758682 : ∀ X1 : G, (M.op y y) = (M.op (M.op X1 y) y) := by
        intro X1
        first
        | (have i₁ := b2e758501 X1
           have i₂ := b2e758048 y
           grind)
        | exact superpose b2e758048 b2e758501
        | exact resolve b2e758501 b2e758048
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e758048 b2e758501
      have b2e758732 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b2e758561 X0 X1
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e758561
        | exact resolve b2e758561 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53 b2e758561
      have b2e758842 : ∀ X1 : G, y = (M.op (M.op X1 y) y) := by
        intro X1
        first
        | (have i₁ := b2e758682 X1
           have i₂ := b2e757110
           grind)
        | exact superpose b2e757110 b2e758682
        | exact resolve b2e758682 b2e757110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e757110 b2e758682
      have b2e758975 : x = y := by
        first
        | (have i₁ := b2e758842 x
           have i₂ := b2e758732 x y
           grind)
        | exact superpose b2e758732 b2e758842
        | exact resolve b2e758842 b2e758732
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e758732 b2e758842
      have b2e759071 : False := by grind
      exact b2e759071
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x y) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X0 X1
           have i₂ := b3e14 (σ X0) (σ X1)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X0) (σ X1)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e676 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e34 x y
           grind)
        | exact superpose b3e34 b3e16
        | (have j1 := b3e34 x y
           grind)
        | exact resolve b3e16 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e34
      have b3e699 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e676
           have r₂ := b3e18
           grind)
        | exact resolve b3e676 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e676
      have b3e702 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b3e699
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e699
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e699 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e699
      have b3e703 : y = (M.op x y) := by grind
      clear b3e702
      have b3e704 : False := by grind
      exact b3e704

/-- `Equation4295`: `x ◇ (x ◇ y) = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pxy_Equation4295 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4295 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4295.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
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
      have b0e63 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e66 : False := by grind
      exact b0e66
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
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
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e34 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e27
          have b5e38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e34 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e34
            | exact resolve b5e34 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e39 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e38
          have b5e43 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X0 X3
               have i₂ := b5e13 X2 X0 X1
               grind)
            | (have i₁ := b5e13 X2 X0 X2
               have i₂ := b5e13 X0 X2 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op X0 y) := by
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
          have b5e46 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 X0) X3 X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | (have i₁ := b5e13 (M.op X0 X1) X1 X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e72 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 y X0 X1
               have i₂ := b5e45 X0
               grind)
            | exact superpose b5e45 b5e13
            | exact resolve b5e13 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e99 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) X1 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e104 : ∀ X0 X1 : G, (M.op X0 y) = (M.op y (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1
               have i₂ := b5e72 X0 X0
               grind)
            | exact superpose b5e72 b5e13
            | exact resolve b5e13 b5e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e728 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e43 X1 X2 (M.op X3 X0) y
               have i₂ := b5e104 X0 X3
               grind)
            | exact superpose b5e104 b5e43
            | exact resolve b5e43 b5e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e104
          have b5e734 : ∀ X0 X1 X2 X3 : G, (M.op X1 y) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e728 X0 X1 X2 X3
               have i₂ := b5e72 X1 X0
               grind)
            | exact superpose b5e72 b5e728
            | exact resolve b5e728 b5e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72 b5e728
          have b5e799 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) X2))) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e46 (σ X0) X1 (σ X0) x
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e46
            | exact resolve b5e46 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e1034 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) X2))) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e799 X0 X1 X2
               have i₂ := b5e99 (M.op X0 X0) X1
               grind)
            | exact superpose b5e99 b5e799
            | exact resolve b5e799 b5e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99 b5e799
          have b5e1091 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) X2))) = (M.op X1 (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1034 X0 X1 X2
               have i₂ := b5e13 X0 (M.op X0 X0) X0
               grind)
            | exact superpose b5e13 b5e1034
            | exact resolve b5e1034 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1034
          have b5e1128 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) X2))) = (M.op X1 (σ (M.op X0 y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1091 X0 X1 X2
               have i₂ := b5e734 X0 X0 X0 X0
               grind)
            | exact superpose b5e734 b5e1091
            | exact resolve b5e1091 b5e734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1091
          have b5e1133 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1128 X0 X1 x
               have i₂ := b5e734 x X1 (σ X0) (σ X0)
               grind)
            | exact superpose b5e734 b5e1128
            | exact resolve b5e1128 b5e734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1128
          have b5e1213 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e31 (M.op (τ X0) (τ X0))
               have i₂ := b5e39 X0
               grind)
            | exact superpose b5e39 b5e31
            | exact resolve b5e31 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e39
          have b5e1219 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b5e1213 X0
               have i₂ := b5e13 (τ X0) (M.op (τ X0) (τ X0)) (τ X0)
               grind)
            | exact superpose b5e13 b5e1213
            | exact resolve b5e1213 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1213
          have b5e1221 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b5e1219 X0
               have i₂ := b5e734 (τ X0) (τ X0) (τ X0) (τ X0)
               grind)
            | exact superpose b5e734 b5e1219
            | exact resolve b5e1219 b5e734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1219
          have b5e1222 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b5e1221 X0
               have i₂ := b5e13 X0 (M.op X0 X0) X0
               grind)
            | exact superpose b5e13 b5e1221
            | exact resolve b5e1221 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1221
          have b5e1223 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b5e1222 X0
               have i₂ := b5e734 X0 X0 X0 X0
               grind)
            | exact superpose b5e734 b5e1222
            | exact resolve b5e1222 b5e734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e734 b5e1222
          have b5e1314 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e1223 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1223
            | exact resolve b5e1223 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1223
          have b5e1454 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e1133 x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1133
            | exact resolve b5e1133 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1133
          have b5e1555 : (σ y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1454 (σ x)
               grind)
            | exact superpose b5e1454 b5e24
            | exact resolve b5e24 b5e1454
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1454
          have b5e1562 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e1555
               have i₂ := b5e1314 x
               grind)
            | exact superpose b5e1314 b5e1555
            | exact resolve b5e1555 b5e1314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1314 b5e1555
          have b5e1583 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e1562
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1562
            | exact resolve b5e1562 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1562
          have b5e1584 : False := by grind
          exact b5e1584
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e33 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X2)) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op X2 X0) X3
               have i₂ := b7e13 X2 X0 X1
               grind)
            | (have i₁ := b7e13 X1 (M.op X2 X0) X2
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 (M.op X2 X0) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | (have i₁ := b7e13 X0 (M.op X0 X1) X2
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X0 X3
               have i₂ := b7e13 X2 X0 X1
               grind)
            | (have i₁ := b7e13 X2 X0 X2
               have i₂ := b7e13 X0 X2 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op X0 (σ y)) := by
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
          have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X2 X0) X3 X1
               have i₂ := b7e13 X0 X1 X2
               grind)
            | (have i₁ := b7e13 (M.op X0 X1) X1 X0
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X2 X2
               have i₂ := b7e13 X2 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) := by
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
          have b7e49 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e57 : (k x y) = (τ (σ x)) := by
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
          have b7e58 : x = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e68 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
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
          have b7e69 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e22
               grind)
            | exact resolve b7e68 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : x = (M.op x y) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e88 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e13
            | exact resolve b7e13 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e89 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b7e13 x y X0
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e13
            | exact resolve b7e13 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e94 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ X0) X1 (σ X0)
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e13
            | exact resolve b7e13 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e95 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ X0) (σ X0) X1
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e13
            | exact resolve b7e13 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e111 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) (σ x) X0
               have i₂ := b7e41 (σ y)
               grind)
            | exact superpose b7e41 b7e13
            | exact resolve b7e13 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e119 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op y (M.op X0 (M.op X0 y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e88 (M.op X1 X0)
               have i₂ := b7e13 X0 y X1
               grind)
            | (have i₁ := b7e88 (M.op y X1)
               have i₂ := b7e13 y X1 x
               grind)
            | exact superpose b7e13 b7e88
            | exact resolve b7e88 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e122 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 y X0 X1
               have i₂ := b7e88 X0
               grind)
            | exact superpose b7e88 b7e13
            | exact resolve b7e13 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e125 : ∀ X0 X1 : G, (M.op y (M.op X0 x)) = (M.op (M.op X1 X0) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e119 X0 X1
               have i₂ := b7e122 X0 X0
               grind)
            | exact superpose b7e122 b7e119
            | exact resolve b7e119 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119
          have b7e128 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X1 X0) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e125 X0 X1
               have i₂ := b7e89 X0
               grind)
            | exact superpose b7e89 b7e125
            | exact resolve b7e125 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89 b7e125
          have b7e149 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 X0 X1 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e150 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X1 (M.op X2 (σ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e36 X1 X2 (σ X0) (σ X0)
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e36
            | exact resolve b7e36 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e151 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (M.op X2 (σ x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e36 X0 X1 (M.op X2 (σ x)) (σ y)
               have i₂ := b7e41 X2
               grind)
            | exact superpose b7e41 b7e36
            | exact resolve b7e36 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e153 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op y X0))) = (M.op X1 (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e36 X1 X2 (M.op y X0) y
               have i₂ := b7e88 X0
               grind)
            | exact superpose b7e88 b7e36
            | exact resolve b7e36 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e174 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op X1 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e88 X1
               have i₂ := b7e36 y y X1 X0
               grind)
            | (have i₁ := b7e88 X1
               have i₂ := b7e36 y X0 X1 y
               grind)
            | exact superpose b7e36 b7e88
            | exact resolve b7e88 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e178 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b7e149 X0 x
               have i₂ := b7e150 y X0 x
               grind)
            | exact superpose b7e150 b7e149
            | exact resolve b7e149 b7e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e149
          have b7e286 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e38 (M.op X0 (σ x))
               have i₂ := b7e41 X0
               grind)
            | exact superpose b7e41 b7e38
            | exact resolve b7e38 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e306 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 (σ y) (σ y) X0 X1
               have i₂ := b7e38 X0
               grind)
            | exact superpose b7e38 b7e36
            | exact resolve b7e36 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e308 : (M.op (σ y) x) = (M.op y (σ y)) := by
            first
            | (have i₁ := b7e122 (σ y) (σ y)
               have i₂ := b7e38 y
               grind)
            | exact superpose b7e38 b7e122
            | exact resolve b7e122 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e332 : ∀ X0 : G, (σ (M.op y y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e286 X0
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e286
            | exact resolve b7e286 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e286
          have b7e678 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ x)) (M.op X1 (M.op X1 (M.op X2 (σ x))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e35 X1 (M.op X2 (σ x)) X0 (σ y)
               have i₂ := b7e41 X2
               grind)
            | exact superpose b7e41 b7e35
            | exact resolve b7e35 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e723 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op X1 (σ y)) (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e35 (σ y) X0 X1 X2
               have i₂ := b7e38 X0
               grind)
            | exact superpose b7e38 b7e35
            | exact resolve b7e35 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e783 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op y y))) = (M.op (M.op X1 (σ y)) (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e723 X0 X1 X2
               have i₂ := b7e150 y X0 X0
               grind)
            | exact superpose b7e150 b7e723
            | exact resolve b7e723 b7e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e723
          have b7e801 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ x)) (M.op X1 (σ y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e678 X0 X1 X2
               have i₂ := b7e151 X1 X1 X2
               grind)
            | exact superpose b7e151 b7e678
            | exact resolve b7e678 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151 b7e678
          have b7e816 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op X1 (σ y)) (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e783 X0 X1 X2
               have i₂ := b7e178 X0
               grind)
            | exact superpose b7e178 b7e783
            | exact resolve b7e783 b7e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e783
          have b7e833 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ x)) (σ (M.op y y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e801 X0 X1 X2
               have i₂ := b7e150 y (M.op X2 (σ x)) X1
               grind)
            | exact superpose b7e150 b7e801
            | exact resolve b7e801 b7e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150 b7e801
          have b7e853 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X2 (σ x)) (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e833 X0 X1 X2
               have i₂ := b7e178 (M.op X2 (σ x))
               grind)
            | exact superpose b7e178 b7e833
            | exact resolve b7e833 b7e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e833
          have b7e864 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op (M.op X0 X1) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e853 X0 X1 x
               have i₂ := b7e332 x
               grind)
            | exact superpose b7e332 b7e853
            | exact resolve b7e853 b7e332
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e332 b7e853
          have b7e1202 : ∀ X0 : G, (M.op y (σ y)) = (M.op (M.op X0 (σ x)) x) := by
            intro X0
            first
            | (have i₁ := b7e174 (σ y) (M.op X0 (σ x))
               have i₂ := b7e41 X0
               grind)
            | exact superpose b7e41 b7e174
            | exact resolve b7e174 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1239 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 x)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e36 X1 X2 (M.op X3 X0) y
               have i₂ := b7e174 X3 X0
               grind)
            | exact superpose b7e174 b7e36
            | exact resolve b7e36 b7e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e1263 : (M.op x x) = (M.op y (σ y)) := by
            first
            | (have i₁ := b7e1202 x
               have i₂ := b7e128 (σ x) x
               grind)
            | exact superpose b7e128 b7e1202
            | exact resolve b7e1202 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128 b7e1202
          have b7e1516 : (M.op x (σ y)) = (M.op (σ y) (M.op y (σ y))) := by
            first
            | (have i₁ := b7e38 x
               have i₂ := b7e308
               grind)
            | exact superpose b7e308 b7e38
            | exact resolve b7e38 b7e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e1529 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x X1))) = (M.op (M.op y (σ y)) (M.op (M.op y (σ y)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 x X1 (σ y) x
               have i₂ := b7e308
               grind)
            | exact superpose b7e308 b7e39
            | exact resolve b7e39 b7e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1541 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x (M.op x X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1529 X0 X1
               have i₂ := b7e816 X0 y (M.op y (σ y))
               grind)
            | exact superpose b7e816 b7e1529
            | exact resolve b7e1529 b7e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e816 b7e1529
          have b7e1554 : (M.op (σ y) (σ (M.op y y))) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e1516
               have i₂ := b7e95 y y
               grind)
            | exact superpose b7e95 b7e1516
            | exact resolve b7e1516 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1516
          have b7e1560 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e1541 X0 X1
               have i₂ := b7e1239 X1 X0 x x
               grind)
            | exact superpose b7e1239 b7e1541
            | exact resolve b7e1541 b7e1239
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1541
          have b7e1571 : (M.op (σ y) (σ y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e1554
               have i₂ := b7e178 (σ y)
               grind)
            | exact superpose b7e178 b7e1554
            | exact resolve b7e1554 b7e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e178 b7e1554
          have b7e1579 : (σ (M.op y y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e1571
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e1571
            | exact resolve b7e1571 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1571
          have b7e1611 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (σ y) X1))) = (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 (σ y) X1 x x
               have i₂ := b7e1579
               grind)
            | exact superpose b7e1579 b7e39
            | exact resolve b7e39 b7e1579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1579
          have b7e1619 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (σ y) X1))) = (M.op X0 (σ (M.op (M.op y y) (M.op y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1611 X0 X1
               have i₂ := b7e94 (M.op y y) X0
               grind)
            | exact superpose b7e94 b7e1611
            | exact resolve b7e1611 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1611
          have b7e1624 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (σ y) X1))) = (M.op X0 (σ (M.op y (M.op y (M.op y y))))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1619 X0 X1
               have i₂ := b7e13 y (M.op y y) y
               grind)
            | exact superpose b7e13 b7e1619
            | exact resolve b7e1619 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1619
          have b7e1628 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (σ y) X1))) = (M.op X0 (σ (M.op y (M.op y x)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1624 X0 X1
               have i₂ := b7e153 y y y
               grind)
            | exact superpose b7e153 b7e1624
            | exact resolve b7e1624 b7e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1624
          have b7e1631 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (σ y) X1))) = (M.op X0 (σ (M.op y (σ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1628 X0 X1
               have i₂ := b7e1560 y y
               grind)
            | exact superpose b7e1560 b7e1628
            | exact resolve b7e1628 b7e1560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1628
          have b7e1634 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (σ y) X1))) = (M.op X0 (σ (M.op x x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1631 X0 X1
               have i₂ := b7e1263
               grind)
            | exact superpose b7e1263 b7e1631
            | exact resolve b7e1631 b7e1263
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1263 b7e1631
          have b7e1636 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 (σ (M.op x x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1634 X0 X1
               have i₂ := b7e1239 X1 X0 (σ y) (σ y)
               grind)
            | exact superpose b7e1239 b7e1634
            | exact resolve b7e1634 b7e1239
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1239 b7e1634
          have b7e1637 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b7e1636 X0 x
               have i₂ := b7e1560 X0 x
               grind)
            | exact superpose b7e1560 b7e1636
            | exact resolve b7e1636 b7e1560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1636
          have b7e1771 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X1 (σ x))) = (M.op (σ x) (M.op (M.op X0 (σ y)) (M.op X2 (σ x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e34 (M.op X0 (σ y)) X2 (σ x) X1
               have i₂ := b7e111 X0
               grind)
            | exact superpose b7e111 b7e34
            | exact resolve b7e34 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e111
          have b7e1800 : ∀ X1 X2 : G, (M.op (σ y) (M.op X1 (σ x))) = (M.op (σ x) (M.op (σ x) (M.op X2 (σ x)))) := by
            intro X1 X2
            first
            | (have i₁ := b7e1771 x X1 X2
               have i₂ := b7e40 (σ x) (M.op x (σ y)) (M.op X2 (σ x))
               grind)
            | exact superpose b7e40 b7e1771
            | exact resolve b7e1771 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e1771
          have b7e1813 : ∀ X1 X2 : G, (M.op (σ y) (M.op X1 (σ x))) = (M.op (M.op X2 (σ x)) (σ (M.op x x))) := by
            intro X1 X2
            first
            | (have i₁ := b7e1800 X1 X2
               have i₂ := b7e94 x (M.op X2 (σ x))
               grind)
            | exact superpose b7e94 b7e1800
            | exact resolve b7e1800 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94 b7e1800
          have b7e1822 : ∀ X1 X2 : G, (M.op (σ y) (M.op X1 (σ x))) = (M.op (M.op X2 (σ x)) (σ y)) := by
            intro X1 X2
            first
            | (have i₁ := b7e1813 X1 X2
               have i₂ := b7e1637 (M.op X2 (σ x))
               grind)
            | exact superpose b7e1637 b7e1813
            | exact resolve b7e1813 b7e1637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1637 b7e1813
          have b7e1830 : ∀ X1 : G, (σ (M.op y y)) = (M.op (σ y) (M.op X1 (σ x))) := by
            intro X1
            first
            | (have i₁ := b7e1822 X1 x
               have i₂ := b7e864 x (σ x)
               grind)
            | exact superpose b7e864 b7e1822
            | exact resolve b7e1822 b7e864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e864 b7e1822
          have b7e1836 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e1830 x
               have i₂ := b7e41 x
               grind)
            | exact superpose b7e41 b7e1830
            | exact resolve b7e1830 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e1830
          have b7e2213 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e1836
               grind)
            | exact superpose b7e1836 b7e14
            | exact resolve b7e14 b7e1836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1836
          have b7e2226 : y = (M.op y y) := by
            first
            | (have i₁ := b7e2213
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e2213
            | exact resolve b7e2213 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2213
          have b7e2346 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e122 X0 y
               have i₂ := b7e2226
               grind)
            | exact superpose b7e2226 b7e122
            | exact resolve b7e122 b7e2226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122
          have b7e2355 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op X0 (M.op y (M.op y X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 y X1 y x
               have i₂ := b7e2226
               grind)
            | exact superpose b7e2226 b7e39
            | exact resolve b7e39 b7e2226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e2367 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op X0 (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e2355 X0 X1
               have i₂ := b7e153 X1 X0 y
               grind)
            | exact superpose b7e153 b7e2355
            | exact resolve b7e2355 b7e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e153 b7e2355
          have b7e2373 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e2367 X0 x
               have i₂ := b7e1560 X0 x
               grind)
            | exact superpose b7e1560 b7e2367
            | exact resolve b7e2367 b7e1560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1560 b7e2367
          have b7e2378 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e2373 X0
               have i₂ := b7e174 y X0
               grind)
            | exact superpose b7e174 b7e2373
            | exact resolve b7e2373 b7e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e174 b7e2373
          have b7e2383 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e2378 X0
               have i₂ := b7e2346 X0
               grind)
            | exact superpose b7e2346 b7e2378
            | exact resolve b7e2378 b7e2346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2346 b7e2378
          have b7e2409 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (M.op (σ y) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e306 (σ X0) (σ X0)
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e306
            | exact resolve b7e306 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e2416 : (M.op x (σ y)) = (M.op (σ y) (M.op y (σ y))) := by
            first
            | (have i₁ := b7e306 x (σ y)
               have i₂ := b7e308
               grind)
            | exact superpose b7e308 b7e306
            | exact resolve b7e306 b7e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e308
          have b7e2424 : (M.op (σ y) y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b7e306 y y
               have i₂ := b7e2226
               grind)
            | exact superpose b7e2226 b7e306
            | exact resolve b7e306 b7e2226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e306
          have b7e2513 : (M.op y y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b7e2424
               have i₂ := b7e2383 y
               grind)
            | exact superpose b7e2383 b7e2424
            | exact resolve b7e2424 b7e2383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2424
          have b7e2517 : (M.op (σ y) (σ (M.op y y))) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e2416
               have i₂ := b7e95 y y
               grind)
            | exact superpose b7e95 b7e2416
            | exact resolve b7e2416 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95 b7e2416
          have b7e2524 : ∀ X0 : G, (M.op (σ y) (σ (M.op X0 X0))) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b7e2409 X0
               have i₂ := b7e2383 (σ X0)
               grind)
            | exact superpose b7e2383 b7e2409
            | exact resolve b7e2409 b7e2383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2409
          have b7e2565 : y = (M.op (σ y) y) := by
            first
            | (have i₁ := b7e2513
               have i₂ := b7e2226
               grind)
            | exact superpose b7e2226 b7e2513
            | exact resolve b7e2513 b7e2226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2226 b7e2513
          have b7e2569 : (M.op x y) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b7e2517
               have i₂ := b7e2383 x
               grind)
            | exact superpose b7e2383 b7e2517
            | exact resolve b7e2517 b7e2383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2383 b7e2517
          have b7e2605 : (M.op x y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b7e2569
               have i₂ := b7e2524 y
               grind)
            | exact superpose b7e2524 b7e2569
            | exact resolve b7e2569 b7e2524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2524 b7e2569
          have b7e2639 : y = (M.op x y) := by
            first
            | (have i₁ := b7e2605
               have i₂ := b7e2565
               grind)
            | exact superpose b7e2565 b7e2605
            | exact resolve b7e2605 b7e2565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2565 b7e2605
          have b7e2673 : False := by grind
          exact b7e2673
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b8e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e831 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e860 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e831
               have r₂ := b8e24
               grind)
            | exact resolve b8e831 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e831
          have b8e866 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e860
               have r₂ := b8e23
               grind)
            | exact resolve b8e860 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e860
          have b8e869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e866
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e866
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e866
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e866
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e866 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e866
          have b8e870 : y = (M.op x y) ∨ x = y := by grind
          clear b8e869
          have b8e871 : x = y := by
            first
            | (have r₁ := b8e870
               have r₂ := b8e22
               grind)
            | exact resolve b8e870 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e870
          have b8e872 : False := by grind
          exact b8e872
