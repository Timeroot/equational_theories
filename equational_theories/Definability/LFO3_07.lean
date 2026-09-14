import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,m(Y,X)) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pypyx_x_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b (M.op b a) ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b (M.op b a))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b (M.op b a) ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b (M.op b a))).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b (M.op b a) ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b (M.op b a))).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y (M.op y x)) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e34 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      have b0e35 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e34 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e35 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e36 (σ X0)
           grind)
        | exact superpose b0e36 b0e17
        | exact resolve b0e17 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e38 X0
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e38
        | exact resolve b0e38 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e38
      have b0e49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X0 X0) (M.op X1 (M.op X1 X0))
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X1 (M.op X1 X0)) (M.op X0 X0)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e49 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e74 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e52 X1 (τ X0)
           grind)
        | exact superpose b0e52 b0e23
        | (have j1 := b0e52 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e52 (σ X1) (σ X0)
           grind)
        | exact superpose b0e52 b0e17
        | (have j1 := b0e52 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e199 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e74 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e74
        | exact resolve b0e74 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e217 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e199 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e199
        | (have j0 := b0e199 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e199 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e199
      have b0e535 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e75 x y
           grind)
        | exact superpose b0e75 b0e18
        | (have j1 := b0e75 x y
           grind)
        | exact resolve b0e18 b0e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e559 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e535
           have i₂ := b0e217 x y
           grind)
        | exact superpose b0e217 b0e535
        | (have j1 := b0e217 (σ x) (σ y)
           grind)
        | (have r₁ := b0e535
           have r₂ := b0e217 x y
           grind)
        | (have r₁ := b0e535
           have r₂ := b0e217 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e535
           have r₂ := b0e217 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e535 b0e217
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e217 b0e535
      have b0e560 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e559
      have b0e567 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e560
           grind)
        | exact superpose b0e560 b0e12
        | exact resolve b0e12 b0e560
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e560
      have b0e598 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e567
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e567
        | exact resolve b0e567 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e567
      have b0e599 : x = y := by grind
      clear b0e598
      have b0e606 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e599
           grind)
        | exact superpose b0e599 b0e18
        | exact resolve b0e18 b0e599
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e599
      have b0e615 : False := by grind
      exact b0e615
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x x) = (M.op y (M.op y x)) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = y := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e28 : (M.op x x) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e20
          | exact resolve b1e20 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x x) := by
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e28
             grind)
          | exact resolve b1e15 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e49 : (M.op x x) = (k x x) := by grind
        clear b1e48
        have b1e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e24
        have b1e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e53
        have b1e57 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e54
          | exact resolve b1e54 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e58 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e57
          | exact resolve b1e57 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e57
        have b1e79 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e25
          | exact resolve b1e25 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e58
        have b1e84 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e79
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e79
          | exact resolve b1e79 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e79
        have b1e85 : False := by grind
        exact b1e85
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X0 X0) (M.op X1 (M.op X1 X0))
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X1 (M.op X1 X0)) (M.op X0 X0)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e65 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e25 X0 X1
             have i₂ := b2e62 X1 (τ X0)
             grind)
          | exact superpose b2e62 b2e25
          | (have j1 := b2e62 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b2e25 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e62 (σ X1) (σ X0)
             grind)
          | exact superpose b2e62 b2e18
          | (have j1 := b2e62 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e145 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e65 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e65
          | exact resolve b2e65 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e163 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e145 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e145
          | (have j0 := b2e145 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b2e145 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e145
        have b2e474 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e66 x y
             grind)
          | exact superpose b2e66 b2e19
          | (have j1 := b2e66 x y
             grind)
          | exact resolve b2e19 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e488 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e474
             have r₂ := b2e22
             grind)
          | exact resolve b2e474 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e474
        have b2e499 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b2e488
             have i₂ := b2e163 x y
             grind)
          | exact superpose b2e163 b2e488
          | (have j1 := b2e163 x y
             grind)
          | (have r₁ := b2e488
             have r₂ := b2e163 x y
             grind)
          | (have r₁ := b2e488
             have r₂ := b2e163 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b2e488
             have r₂ := b2e163 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b2e488 b2e163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163 b2e488
        have b2e500 : x = y := by grind
        clear b2e499
        have b2e508 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e500
             grind)
          | exact superpose b2e500 b2e22
          | exact resolve b2e22 b2e500
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e500
        have b2e513 : False := by grind
        exact b2e513
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e33 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e34 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b3e33
        have b3e35 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e34
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e34
          | exact resolve b3e34 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e45 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b3e46 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e45 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e69 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e35
        have b3e72 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e69
             have i₂ := b3e47 y
             grind)
          | exact superpose b3e47 b3e69
          | exact resolve b3e69 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e69
        have b3e73 : False := by grind
        exact b3e73
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e46 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            grind
          have b4e47 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e47 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e48 (σ X0)
               grind)
            | exact superpose b4e48 b4e19
            | exact resolve b4e19 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e52 X0
               have i₂ := b4e48 X0
               grind)
            | exact superpose b4e48 b4e52
            | exact resolve b4e52 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e52
          have b4e112 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
          clear b4e57
          have b4e117 : False := by grind
          exact b4e117
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X1
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X0 X0) (M.op X1 (M.op X1 X0))
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X1 (M.op X1 X0)) (M.op X0 X0)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e66 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e66 (σ X1) (σ X0)
             grind)
          | exact superpose b6e66 b6e18
          | (have j1 := b6e66 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b6e18 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X1 X0
             have i₂ := b6e66 (τ X1) X0
             grind)
          | exact superpose b6e66 b6e24
          | (have j1 := b6e66 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
             grind)
          | exact resolve b6e24 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e66
        have b6e198 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e70 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e70
          | exact resolve b6e70 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e214 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e198 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e198
          | (have j0 := b6e198 (σ (k X0 X1)) (σ (M.op X1 X0))
             grind)
          | exact resolve b6e198 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e198
        have b6e556 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e69 x y
             grind)
          | exact superpose b6e69 b6e19
          | (have j1 := b6e69 x y
             grind)
          | exact resolve b6e19 b6e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e583 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e556
             have i₂ := b6e214 y x
             grind)
          | exact superpose b6e214 b6e556
          | (have j1 := b6e214 (σ x) (σ y)
             grind)
          | (have r₁ := b6e556
             have r₂ := b6e214 y x
             grind)
          | (have r₁ := b6e556
             have r₂ := b6e214 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b6e556
             have r₂ := b6e214 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b6e556 b6e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e214 b6e556
        have b6e584 : (σ x) = (σ y) ∨ x = y := by grind
        clear b6e583
        have b6e586 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e584
             have r₂ := b6e21
             grind)
          | exact resolve b6e584 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e584
        have b6e643 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e586
             grind)
          | exact superpose b6e586 b6e13
          | exact resolve b6e13 b6e586
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e586
        have b6e676 : x = y := by
          first
          | (have i₁ := b6e643
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e643
          | exact resolve b6e643 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e643
        have b6e681 : False := by grind
        exact b6e681
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
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
          have b8e60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X1 (M.op X1 X0))
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X1 (M.op X1 X0)) (M.op X0 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e63 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e63 (σ X1) (σ X0)
               grind)
            | exact superpose b8e63 b8e19
            | (have j1 := b8e63 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e63 (τ X1) X0
               grind)
            | exact superpose b8e63 b8e26
            | (have j1 := b8e63 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
               grind)
            | exact resolve b8e26 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e63
          have b8e146 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e68 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e68
            | exact resolve b8e68 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e162 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e146 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e146
            | (have j0 := b8e146 (σ (k X0 X1)) (σ (M.op X1 X0))
               grind)
            | exact resolve b8e146 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146
          have b8e475 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e67 x y
               grind)
            | exact superpose b8e67 b8e20
            | (have j1 := b8e67 x y
               grind)
            | exact resolve b8e20 b8e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e489 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e475
               have r₂ := b8e24
               grind)
            | exact resolve b8e475 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e475
          have b8e498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e489
               have i₂ := b8e162 y x
               grind)
            | exact superpose b8e162 b8e489
            | (have j1 := b8e162 x y
               grind)
            | (have r₁ := b8e489
               have r₂ := b8e162 y x
               grind)
            | (have r₁ := b8e489
               have r₂ := b8e162 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e489
               have r₂ := b8e162 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e489 b8e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e162 b8e489
          have b8e499 : x = y := by grind
          clear b8e498
          have b8e501 : False := by grind
          exact b8e501

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_y_pyx_y_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
      have b0e38 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X2
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X0 X2
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X0
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e38 X0 X2 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e61 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e39 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e61 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
      have b0e191 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e62 (σ X1) (σ X0)
           grind)
        | exact superpose b0e62 b0e17
        | (have j1 := b0e62 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e193 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e62 (τ X1) X0
           grind)
        | exact superpose b0e62 b0e21
        | (have j1 := b0e62 (τ X1) X0
           grind)
        | exact resolve b0e21 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e62
      have b0e2638 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e193 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e193
        | exact resolve b0e193 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e193
      have b0e2726 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e2638 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e2638
        | (have j0 := b0e2638 X0 X1
           grind)
        | exact resolve b0e2638 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2638
      have b0e3165 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e191 x y
           grind)
        | exact superpose b0e191 b0e18
        | (have j1 := b0e191 x y
           grind)
        | exact resolve b0e18 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3189 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e191 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191
      have b0e10393 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e3189 (τ X1) (τ X0)
           have i₂ := b0e64 X1 X0
           grind)
        | exact superpose b0e64 b0e3189
        | (have j0 := b0e3189 (τ X1) (τ X0)
           grind)
        | exact resolve b0e3189 b0e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e10454 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e10393 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e10393
        | (have j0 := b0e10393 X0 X1
           grind)
        | exact resolve b0e10393 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10393
      have b0e10482 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e10454 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e10454
        | (have j0 := b0e10454 X0 X1
           grind)
        | exact resolve b0e10454 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10454
      have b0e10497 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e10482 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e10482
        | (have j0 := b0e10482 X0 X1
           grind)
        | exact resolve b0e10482 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10482
      have b0e10504 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e10497 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e10497
        | (have j0 := b0e10497 X0 X1
           grind)
        | exact resolve b0e10497 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10497
      have b0e26733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e3165
           have i₂ := b0e2726 y x
           grind)
        | exact superpose b0e2726 b0e3165
        | (have j1 := b0e2726 (σ y) (σ x)
           grind)
        | (have r₁ := b0e3165
           have r₂ := b0e2726 y x
           grind)
        | exact resolve b0e3165 b0e2726
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e26734 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e26733
      have b0e27173 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e26734
           grind)
        | exact superpose b0e26734 b0e18
        | exact resolve b0e18 b0e26734
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27174 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e26734
           grind)
        | exact superpose b0e26734 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e26734
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e26734
           grind)
        | exact resolve b0e15 b0e26734
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27175 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
      clear b0e27174
      have b0e27176 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e27175
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e27175
        | exact resolve b0e27175 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27175
      have b0e241554 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ y) X0
           have i₂ := b0e27176
           grind)
        | exact superpose b0e27176 b0e14
        | (have j0 := b0e14 (σ y) X0
           grind)
        | (have r₁ := b0e14 (σ y) x
           have r₂ := b0e27176
           grind)
        | exact resolve b0e14 b0e27176
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27176
      have b0e241557 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        intro X0
        first
        | (have j0 := b0e241554 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e241554
      have b0e335467 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 (σ y))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e48 y X0
           have i₂ := b0e241557 X0
           grind)
        | exact superpose b0e241557 b0e48
        | exact resolve b0e48 b0e241557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e241557
      have b0e362678 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e335467 (σ x)
           have i₂ := b0e26734
           grind)
        | exact superpose b0e26734 b0e335467
        | exact resolve b0e335467 b0e26734
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26734 b0e335467
      have b0e362696 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
      clear b0e362678
      have b0e362702 : x = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e362696
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e362696
        | exact resolve b0e362696 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e362696
      have b0e362704 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have j1 := b0e10504 y x
           grind)
        | (have r₁ := b0e362702
           have r₂ := b0e10504 y x
           grind)
        | exact resolve b0e362702 b0e10504
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10504 b0e362702
      have b0e362751 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e2726 y x
           have i₂ := b0e362704
           grind)
        | exact superpose b0e362704 b0e2726
        | (have j0 := b0e2726 y x
           grind)
        | exact resolve b0e2726 b0e362704
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2726 b0e362704
      have b0e363121 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
      clear b0e362751
      have b0e363414 : x = (M.op x y) := by
        first
        | (have r₁ := b0e363121
           have r₂ := b0e27173
           grind)
        | exact resolve b0e363121 b0e27173
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27173 b0e363121
      have b0e363655 : x ≠ x ∨ y = (M.op y y) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e363414
           grind)
        | exact superpose b0e363414 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e363414
           grind)
        | exact resolve b0e15 b0e363414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e363656 : x = (k y x) ∨ y = (M.op y y) := by grind
      clear b0e363655
      have b0e363727 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e3189 x y
           have i₂ := b0e363656
           grind)
        | exact superpose b0e363656 b0e3189
        | (have j0 := b0e3189 x y
           grind)
        | exact resolve b0e3189 b0e363656
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3189 b0e363656
      have b0e363822 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
      clear b0e363727
      have b0e363908 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e363822
           grind)
        | exact superpose b0e363822 b0e18
        | exact resolve b0e18 b0e363822
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e363822
      have b0e363913 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e363908
           have i₂ := b0e363414
           grind)
        | exact superpose b0e363414 b0e363908
        | exact resolve b0e363908 b0e363414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e363908
      have b0e363914 : y = (M.op y y) := by grind
      clear b0e363913
      have b0e363938 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 y X0
           have i₂ := b0e363914
           grind)
        | exact superpose b0e363914 b0e14
        | (have j0 := b0e14 y X0
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e363914
           grind)
        | exact resolve b0e14 b0e363914
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e363914
      have b0e363943 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e363938 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e363938
      have b0e364009 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e3165
           have i₂ := b0e363943 x
           grind)
        | exact superpose b0e363943 b0e3165
        | exact resolve b0e3165 b0e363943
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3165 b0e363943
      have b0e364319 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear b0e364009
      have b0e364505 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e364319
           grind)
        | exact superpose b0e364319 b0e18
        | exact resolve b0e18 b0e364319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e364319
      have b0e364510 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e364505
           have i₂ := b0e363414
           grind)
        | exact superpose b0e363414 b0e364505
        | exact resolve b0e364505 b0e363414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e363414 b0e364505
      have b0e364511 : False := by grind
      exact b0e364511
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
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
        have b1e26 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b1e25 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e39 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X1) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e130 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e39 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e132 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e130 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e130
        have b1e377 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e132 x
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e132
          | (have j0 := b1e132 x
             grind)
          | exact resolve b1e132 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e132
        have b1e383 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have r₁ := b1e377
             have r₂ := b1e21
             grind)
          | exact resolve b1e377 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e377
        have b1e388 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e383
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e383
          | exact resolve b1e383 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e383
        have b1e389 : False := by grind
        exact b1e389
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
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
        have b2e26 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b2e25 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e112 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e32 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e114 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e112 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e112
        have b2e333 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e114 x
             have i₂ := b2e26 x
             grind)
          | exact superpose b2e26 b2e114
          | (have j0 := b2e114 x
             grind)
          | exact resolve b2e114 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e114
        have b2e339 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have r₁ := b2e333
             have r₂ := b2e21
             grind)
          | exact resolve b2e333 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e333
        have b2e344 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e339
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e339
          | exact resolve b2e339 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e339
        have b2e345 : False := by grind
        exact b2e345
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b3e26 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e25 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e28 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e26 (σ X0)
             grind)
          | exact superpose b3e26 b3e18
          | exact resolve b3e18 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e60 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e28 x
             grind)
          | exact superpose b3e28 b3e22
          | exact resolve b3e22 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e89 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e13
          | exact resolve b3e13 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e91 : x = (k x x) := by
          first
          | (have i₁ := b3e89
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e89
          | exact resolve b3e89 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89
        have b3e137 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e91
             grind)
          | exact superpose b3e91 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91
        have b3e138 : x = (M.op x x) := by grind
        clear b3e137
        have b3e142 : False := by grind
        exact b3e142
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b4e36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          clear b4e26
          have b4e52 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X1
               have j1 := b4e18 X0 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X0
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e55 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e52 X0 X2 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e58 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          clear b4e30
          have b4e103 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e55 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e104 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103
          have b4e161 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e104 (σ X1) (σ X0)
               grind)
            | exact superpose b4e104 b4e19
            | (have j1 := b4e104 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e163 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X1 X0
               have i₂ := b4e104 (τ X1) X0
               grind)
            | exact superpose b4e104 b4e25
            | (have j1 := b4e104 (τ X1) X0
               grind)
            | exact resolve b4e25 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e104
          have b4e1348 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e163 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e163
            | exact resolve b4e163 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163
          have b4e1413 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e1348 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e1348
            | (have j0 := b4e1348 X0 X1
               grind)
            | exact resolve b4e1348 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1348
          have b4e1828 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e161 x y
               grind)
            | exact superpose b4e161 b4e20
            | (have j1 := b4e161 x y
               grind)
            | exact resolve b4e20 b4e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1836 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e161 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e161
          have b4e1858 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1836 (τ X1) (τ X0)
               have i₂ := b4e58 X1 X0
               grind)
            | exact superpose b4e58 b4e1836
            | (have j0 := b4e1836 (τ X1) (τ X0)
               grind)
            | exact resolve b4e1836 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58
          have b4e1870 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1858 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e1858
            | (have j0 := b4e1858 X0 X1
               grind)
            | exact resolve b4e1858 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1858
          have b4e1872 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1870 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e1870
            | (have j0 := b4e1870 X0 X1
               grind)
            | exact resolve b4e1870 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1870
          have b4e1873 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e1872 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1872
            | (have j0 := b4e1872 X0 X1
               grind)
            | exact resolve b4e1872 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1872
          have b4e1874 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e1873 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1873
            | (have j0 := b4e1873 X0 X1
               grind)
            | exact resolve b4e1873 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1873
          have b4e2682 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1828
               have i₂ := b4e1413 y x
               grind)
            | exact superpose b4e1413 b4e1828
            | (have j1 := b4e1413 (σ y) (σ x)
               grind)
            | (have r₁ := b4e1828
               have r₂ := b4e1413 y x
               grind)
            | exact resolve b4e1828 b4e1413
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2683 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e2682
          have b4e2843 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e2683
               grind)
            | exact superpose b4e2683 b4e20
            | exact resolve b4e20 b4e2683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2844 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e2683
               grind)
            | exact superpose b4e2683 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e2683
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e2683
               grind)
            | exact resolve b4e17 b4e2683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2845 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e2844
          have b4e2846 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e2845
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e2845
            | exact resolve b4e2845 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2845
          have b4e13517 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e16 (σ y) X0
               have i₂ := b4e2846
               grind)
            | exact superpose b4e2846 b4e16
            | (have j0 := b4e16 (σ y) X0
               grind)
            | (have r₁ := b4e16 (σ y) x
               have r₂ := b4e2846
               grind)
            | exact resolve b4e16 b4e2846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2846
          have b4e13520 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b4e13517 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13517
          have b4e30784 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 (σ y))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e36 y X0
               have i₂ := b4e13520 X0
               grind)
            | exact superpose b4e13520 b4e36
            | exact resolve b4e36 b4e13520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e13520
          have b4e82667 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e30784 (σ x)
               have i₂ := b4e2683
               grind)
            | exact superpose b4e2683 b4e30784
            | exact resolve b4e30784 b4e2683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2683 b4e30784
          have b4e82934 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
          clear b4e82667
          have b4e82945 : x = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e82934
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e82934
            | exact resolve b4e82934 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82934
          have b4e82947 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e1874 y x
               grind)
            | (have r₁ := b4e82945
               have r₂ := b4e1874 y x
               grind)
            | exact resolve b4e82945 b4e1874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1874 b4e82945
          have b4e83460 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1413 y x
               have i₂ := b4e82947
               grind)
            | exact superpose b4e82947 b4e1413
            | (have j0 := b4e1413 y x
               grind)
            | exact resolve b4e1413 b4e82947
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1413 b4e82947
          have b4e83607 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b4e83460
          have b4e83642 : x = (M.op x y) := by
            first
            | (have r₁ := b4e83607
               have r₂ := b4e2843
               grind)
            | exact resolve b4e83607 b4e2843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2843 b4e83607
          have b4e84162 : x ≠ x ∨ y = (M.op y y) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e83642
               grind)
            | exact superpose b4e83642 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e83642
               grind)
            | exact resolve b4e17 b4e83642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e84163 : x = (k y x) ∨ y = (M.op y y) := by grind
          clear b4e84162
          have b4e84609 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e1836 x y
               have i₂ := b4e84163
               grind)
            | exact superpose b4e84163 b4e1836
            | (have j0 := b4e1836 x y
               grind)
            | exact resolve b4e1836 b4e84163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1836 b4e84163
          have b4e84666 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
          clear b4e84609
          have b4e85967 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e84666
               grind)
            | exact superpose b4e84666 b4e20
            | exact resolve b4e20 b4e84666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84666
          have b4e85972 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e85967
               have i₂ := b4e83642
               grind)
            | exact superpose b4e83642 b4e85967
            | exact resolve b4e85967 b4e83642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85967
          have b4e85973 : y = (M.op y y) := by grind
          clear b4e85972
          have b4e86459 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e85973
               grind)
            | exact superpose b4e85973 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e85973
               grind)
            | exact resolve b4e16 b4e85973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85973
          have b4e86462 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e86459 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86459
          have b4e86983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e1828
               have i₂ := b4e86462 x
               grind)
            | exact superpose b4e86462 b4e1828
            | exact resolve b4e1828 b4e86462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1828 b4e86462
          have b4e87123 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e86983
          have b4e87893 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e87123
               grind)
            | exact superpose b4e87123 b4e20
            | exact resolve b4e20 b4e87123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87123
          have b4e87898 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e87893
               have i₂ := b4e83642
               grind)
            | exact superpose b4e83642 b4e87893
            | exact resolve b4e87893 b4e83642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83642 b4e87893
          have b4e87899 : False := by grind
          exact b4e87899
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e39 : y ≠ y ∨ x = (M.op x x) ∨ y = (k x y) := by
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
          have b5e40 : x = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e39
          have b5e41 : y = (k x y) := by
            first
            | (have r₁ := b5e40
               have r₂ := b5e21
               grind)
            | exact resolve b5e40 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e138 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e45 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e568 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e138 y x
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e138
            | (have j0 := b5e138 x x
               grind)
            | exact resolve b5e138 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e138
          have b5e571 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e568
          have b5e574 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e571
               have r₂ := b5e23
               grind)
            | exact resolve b5e571 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e571
          have b5e578 : False := by grind
          exact b5e578
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b6e26 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b6e25 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e28 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e26 (σ X0)
             grind)
          | exact superpose b6e26 b6e18
          | exact resolve b6e18 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e65 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e28 x
             grind)
          | exact superpose b6e28 b6e22
          | exact resolve b6e22 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e103 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e13
          | exact resolve b6e13 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e114 : x = (k x x) := by
          first
          | (have i₁ := b6e103
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e103
          | exact resolve b6e103 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e103
        have b6e138 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e114
             grind)
          | exact superpose b6e114 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114
        have b6e139 : x = (M.op x x) := by grind
        clear b6e138
        have b6e143 : False := by grind
        exact b6e143
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e39 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e40 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e39
          have b7e41 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e40
               have r₂ := b7e23
               grind)
            | exact resolve b7e40 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e42 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e41
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e41
            | exact resolve b7e41 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e42
               grind)
            | exact superpose b7e42 b7e14
            | exact resolve b7e14 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : y = (k x y) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e45
            | exact resolve b7e45 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e61 : y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e62 : y = (M.op y x) ∨ x = (M.op x x) := by grind
          clear b7e61
          have b7e64 : x = (M.op x x) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e66 : False := by grind
          exact b7e66
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
          have b8e36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          clear b8e26
          have b8e39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e52 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X2
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e55 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e52 X0 X2 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e104 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e105 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e104 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e109 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e105 (σ X1) (σ X0)
               grind)
            | exact superpose b8e105 b8e19
            | (have j1 := b8e105 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e111 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e105 (τ X1) X0
               grind)
            | exact superpose b8e105 b8e25
            | (have j1 := b8e105 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e105
          have b8e1360 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e111 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e111
            | exact resolve b8e111 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111
          have b8e1426 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1360 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1360
            | (have j0 := b8e1360 X0 X1
               grind)
            | exact resolve b8e1360 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1360
          have b8e1797 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e109 x y
               grind)
            | exact superpose b8e109 b8e20
            | (have j1 := b8e109 x y
               grind)
            | exact resolve b8e20 b8e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1805 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e109 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e1913 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1805 (τ X1) (τ X0)
               have i₂ := b8e39 X1 X0
               grind)
            | exact superpose b8e39 b8e1805
            | (have j0 := b8e1805 (τ X1) (τ X0)
               grind)
            | exact resolve b8e1805 b8e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39
          have b8e1924 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1913 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e1913
            | (have j0 := b8e1913 X0 X1
               grind)
            | exact resolve b8e1913 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1913
          have b8e1926 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1924 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e1924
            | (have j0 := b8e1924 X0 X1
               grind)
            | exact resolve b8e1924 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1924
          have b8e1927 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1926 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1926
            | (have j0 := b8e1926 X0 X1
               grind)
            | exact resolve b8e1926 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1926
          have b8e1928 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1927 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1927
            | (have j0 := b8e1927 X0 X1
               grind)
            | exact resolve b8e1927 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1927
          have b8e2641 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1797
               have i₂ := b8e1426 y x
               grind)
            | exact superpose b8e1426 b8e1797
            | (have j1 := b8e1426 (σ y) (σ x)
               grind)
            | (have r₁ := b8e1797
               have r₂ := b8e1426 y x
               grind)
            | exact resolve b8e1797 b8e1426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2642 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e2641
          have b8e2802 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2642
               grind)
            | exact superpose b8e2642 b8e20
            | exact resolve b8e20 b8e2642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2803 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e2642
               grind)
            | exact superpose b8e2642 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e2642
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e2642
               grind)
            | exact resolve b8e17 b8e2642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2804 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e2803
          have b8e2805 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e2804
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e2804
            | exact resolve b8e2804 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2804
          have b8e13288 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e16 (σ y) X0
               have i₂ := b8e2805
               grind)
            | exact superpose b8e2805 b8e16
            | (have j0 := b8e16 (σ y) X0
               grind)
            | (have r₁ := b8e16 (σ y) x
               have r₂ := b8e2805
               grind)
            | exact resolve b8e16 b8e2805
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2805
          have b8e13291 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e13288 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13288
          have b8e30051 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 (σ y))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e36 y X0
               have i₂ := b8e13291 X0
               grind)
            | exact superpose b8e13291 b8e36
            | exact resolve b8e36 b8e13291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36 b8e13291
          have b8e77171 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e30051 (σ x)
               have i₂ := b8e2642
               grind)
            | exact superpose b8e2642 b8e30051
            | exact resolve b8e30051 b8e2642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2642 b8e30051
          have b8e77431 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
          clear b8e77171
          have b8e77442 : x = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e77431
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e77431
            | exact resolve b8e77431 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77431
          have b8e77444 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e1928 y x
               grind)
            | (have r₁ := b8e77442
               have r₂ := b8e1928 y x
               grind)
            | exact resolve b8e77442 b8e1928
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1928 b8e77442
          have b8e78187 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1426 y x
               have i₂ := b8e77444
               grind)
            | exact superpose b8e77444 b8e1426
            | (have j0 := b8e1426 y x
               grind)
            | exact resolve b8e1426 b8e77444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1426 b8e77444
          have b8e78322 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b8e78187
          have b8e78356 : x = (M.op x y) := by
            first
            | (have r₁ := b8e78322
               have r₂ := b8e2802
               grind)
            | exact resolve b8e78322 b8e2802
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2802 b8e78322
          have b8e79091 : x ≠ x ∨ y = (M.op y y) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e78356
               grind)
            | exact superpose b8e78356 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e78356
               grind)
            | exact resolve b8e17 b8e78356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e79092 : x = (k y x) ∨ y = (M.op y y) := by grind
          clear b8e79091
          have b8e79963 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1805 x y
               have i₂ := b8e79092
               grind)
            | exact superpose b8e79092 b8e1805
            | (have j0 := b8e1805 x y
               grind)
            | exact resolve b8e1805 b8e79092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1805 b8e79092
          have b8e80020 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
          clear b8e79963
          have b8e81090 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e80020
               grind)
            | exact superpose b8e80020 b8e20
            | exact resolve b8e20 b8e80020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80020
          have b8e81095 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e81090
               have i₂ := b8e78356
               grind)
            | exact superpose b8e78356 b8e81090
            | exact resolve b8e81090 b8e78356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81090
          have b8e81096 : y = (M.op y y) := by grind
          clear b8e81095
          have b8e81439 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e16 y X0
               have i₂ := b8e81096
               grind)
            | exact superpose b8e81096 b8e16
            | (have j0 := b8e16 y X0
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e81096
               grind)
            | exact resolve b8e16 b8e81096
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81096
          have b8e81442 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e81439 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81439
          have b8e81962 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1797
               have i₂ := b8e81442 x
               grind)
            | exact superpose b8e81442 b8e1797
            | exact resolve b8e1797 b8e81442
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1797 b8e81442
          have b8e82097 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e81962
          have b8e82691 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e82097
               grind)
            | exact superpose b8e82097 b8e20
            | exact resolve b8e20 b8e82097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82097
          have b8e82696 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e82691
               have i₂ := b8e78356
               grind)
            | exact superpose b8e78356 b8e82691
            | exact resolve b8e82691 b8e78356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78356 b8e82691
          have b8e82697 : False := by grind
          exact b8e82697

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,m(Y,X)) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pypyx_pyx_y_pyx_y_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b (M.op b a) ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b (M.op b a))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b (M.op b a) ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b (M.op b a))).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b (M.op b a) ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b (M.op b a))).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y (M.op y x)) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op y (M.op y x)) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
      have b0e27 : (M.op (M.op y x) y) ≠ (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op y x) y) := by
        first
        | (have i₁ := b0e14 (M.op y x) y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : (M.op (M.op (σ y) (σ x)) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ x)) (σ y)) := by
        first
        | (have i₁ := b0e14 (M.op (σ y) (σ x)) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e30
      have b0e32 : (M.op y x) = (k x y) := by grind
      clear b0e29
      have b0e33 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e31
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e31
        | exact resolve b0e31 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e34 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e33
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e33
        | exact resolve b0e33 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e33
      have b0e48 : (M.op (M.op y x) y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k (M.op y x) y) := by
        first
        | (have i₁ := b0e16 (M.op y x) y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e16
        | exact resolve b0e16 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : (M.op (M.op (σ y) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ x)) (σ y)) := by
        first
        | (have i₁ := b0e16 (M.op (σ y) (σ x)) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e16
        | exact resolve b0e16 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e54 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e56 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ x)) (σ y)) := by
        first
        | (have r₁ := b0e49
           have r₂ := b0e28
           grind)
        | exact resolve b0e49 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e49
      have b0e57 : (M.op x y) = (k (M.op y x) y) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e48
           have r₂ := b0e27
           grind)
        | exact resolve b0e48 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e48
      have b0e58 : (M.op (σ x) (σ y)) = (k (σ (M.op y x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e56
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e56
        | exact resolve b0e56 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e59 : (M.op (σ x) (σ y)) = (σ (k (M.op y x) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e58
           have i₂ := b0e17 (M.op y x) y
           grind)
        | exact superpose b0e17 b0e58
        | exact resolve b0e58 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e55 (σ X1) (σ X0)
           grind)
        | exact superpose b0e55 b0e17
        | (have j1 := b0e55 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e55 (τ X1) X0
           grind)
        | exact superpose b0e55 b0e21
        | (have j1 := b0e55 (τ X1) X0
           grind)
        | exact resolve b0e21 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e55
      have b0e108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e59
           have i₂ := b0e57
           grind)
        | exact superpose b0e57 b0e59
        | exact resolve b0e59 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57 b0e59
      have b0e116 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e108
           have r₂ := b0e18
           grind)
        | exact resolve b0e108 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108
      have b0e125 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e116
           grind)
        | exact superpose b0e116 b0e18
        | exact resolve b0e18 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e126 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e16 (σ y) (σ x)
           have i₂ := b0e116
           grind)
        | exact superpose b0e116 b0e16
        | exact resolve b0e16 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e128 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e116
           grind)
        | exact superpose b0e116 b0e14
        | exact resolve b0e14 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116
      have b0e129 : (M.op (σ x) (σ y)) ≠ (σ (M.op y x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e128
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e128
        | exact resolve b0e128 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128
      have b0e131 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e126
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e126
        | exact resolve b0e126 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126
      have b0e132 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) ≠ (σ (M.op y x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e129
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e129
        | exact resolve b0e129 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129
      have b0e134 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e131
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e131
        | exact resolve b0e131 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e131
      have b0e135 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e134
           have r₂ := b0e132
           grind)
        | exact resolve b0e134 b0e132
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132 b0e134
      have b0e284 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e71 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e71
        | exact resolve b0e71 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71
      have b0e309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e284 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e284
        | (have j0 := b0e284 X0 X1
           grind)
        | exact resolve b0e284 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e284
      have b0e449 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e70 x y
           grind)
        | exact superpose b0e70 b0e18
        | (have j1 := b0e70 x y
           grind)
        | exact resolve b0e18 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e837 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e449
           have i₂ := b0e309 y x
           grind)
        | exact superpose b0e309 b0e449
        | (have j1 := b0e309 (σ y) (σ x)
           grind)
        | (have r₁ := b0e449
           have r₂ := b0e309 y x
           grind)
        | exact resolve b0e449 b0e309
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e449
      have b0e838 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e837
      have b0e842 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e838
           grind)
        | exact superpose b0e838 b0e18
        | exact resolve b0e18 b0e838
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e849 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e838
           grind)
        | exact superpose b0e838 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e838
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e838
           grind)
        | exact resolve b0e15 b0e838
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e850 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e838
           grind)
        | exact superpose b0e838 b0e14
        | exact resolve b0e14 b0e838
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e838
      have b0e851 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
      clear b0e849
      have b0e852 : (σ (M.op y x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e850
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e850
        | exact resolve b0e850 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e850
      have b0e853 : (σ (M.op y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e851
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e851
        | exact resolve b0e851 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e851
      have b0e859 : (σ x) = (σ (k y x)) ∨ (σ (M.op y x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e852
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e852
        | exact resolve b0e852 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e852
      have b0e860 : (σ x) = (σ (k y x)) ∨ (σ (M.op y x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e853
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e853
        | exact resolve b0e853 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e853
      have b0e861 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e860
           have r₂ := b0e859
           grind)
        | exact resolve b0e860 b0e859
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e859 b0e860
      have b0e1014 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e309 y x
           have i₂ := b0e861
           grind)
        | exact superpose b0e861 b0e309
        | (have j0 := b0e309 y x
           grind)
        | exact resolve b0e309 b0e861
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e309 b0e861
      have b0e1040 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
      clear b0e1014
      have b0e1063 : x = (M.op x y) := by
        first
        | (have r₁ := b0e1040
           have r₂ := b0e842
           grind)
        | exact resolve b0e1040 b0e842
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e842 b0e1040
      have b0e1152 : (σ x) ≠ (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e125
           have i₂ := b0e1063
           grind)
        | exact superpose b0e1063 b0e125
        | exact resolve b0e125 b0e1063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125
      have b0e1155 : x ≠ x ∨ (M.op y x) = (M.op x x) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e1063
           grind)
        | exact superpose b0e1063 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e1063
           grind)
        | exact resolve b0e15 b0e1063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1156 : (M.op y x) ≠ (M.op x x) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e1063
           grind)
        | exact superpose b0e1063 b0e14
        | exact resolve b0e14 b0e1063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1157 : (M.op y x) = (M.op x x) ∨ x = (k y x) := by grind
      clear b0e1155
      have b0e1158 : x = (k y x) := by
        first
        | (have r₁ := b0e1157
           have r₂ := b0e1156
           grind)
        | exact resolve b0e1157 b0e1156
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1156 b0e1157
      have b0e1250 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e135
           have i₂ := b0e1158
           grind)
        | exact superpose b0e1158 b0e135
        | exact resolve b0e135 b0e1158
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135 b0e1158
      have b0e1259 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e1250
      have b0e1261 : x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e1259
           have i₂ := b0e1063
           grind)
        | exact superpose b0e1063 b0e1259
        | exact resolve b0e1259 b0e1063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1259
      have b0e1262 : x = y := by
        first
        | (have r₁ := b0e1261
           have r₂ := b0e1152
           grind)
        | exact resolve b0e1261 b0e1152
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1152 b0e1261
      have b0e1372 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1262
           grind)
        | exact superpose b0e1262 b0e18
        | exact resolve b0e18 b0e1262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1378 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e34
           have i₂ := b0e1262
           grind)
        | exact superpose b0e1262 b0e34
        | exact resolve b0e34 b0e1262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e1393 : y = (M.op y y) := by
        first
        | (have i₁ := b0e1063
           have i₂ := b0e1262
           grind)
        | exact superpose b0e1262 b0e1063
        | exact resolve b0e1063 b0e1262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1063 b0e1262
      have b0e1402 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e1378
           have i₂ := b0e1393
           grind)
        | exact superpose b0e1393 b0e1378
        | exact resolve b0e1378 b0e1393
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1378
      have b0e1407 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e1372
           have i₂ := b0e1393
           grind)
        | exact superpose b0e1393 b0e1372
        | exact resolve b0e1372 b0e1393
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1372 b0e1393
      have b0e1413 : False := by grind
      exact b0e1413
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op y (M.op y x)) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (k x y) := by
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
        have b1e41 : (M.op y x) = (k x y) := by grind
        clear b1e40
        have b1e42 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e44 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e42
        have b1e45 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e23
             grind)
          | exact resolve b1e44 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e44
        have b1e46 : (σ y) = (σ (k x y)) := by
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
        have b1e47 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e46
          | exact resolve b1e46 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e46
        have b1e50 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e13
          | exact resolve b1e13 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e51 : y = (M.op y x) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e50
          | exact resolve b1e50 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X0 X1
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e59 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e60 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e63 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e20
          | exact resolve b1e20 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e60 (σ X1) (σ X0)
             grind)
          | exact superpose b1e60 b1e18
          | (have j1 := b1e60 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e73 : (M.op y x) = (M.op x (M.op y y)) ∨ x = (M.op y y) ∨ (M.op y y) = (k y x) := by
          first
          | (have i₁ := b1e17 y x
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e17
          | exact resolve b1e17 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74 : x ≠ (M.op y y) ∨ (M.op y x) = (M.op x (M.op y y)) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e16
          | (have j0 := b1e16 y x
             grind)
          | exact resolve b1e16 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : (M.op y x) ≠ (M.op x (M.op y y)) ∨ (M.op y y) = (k y x) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e15
          | exact resolve b1e15 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : y ≠ (M.op x (M.op y y)) ∨ (M.op y y) = (k y x) := by
          first
          | (have i₁ := b1e75
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e75
          | exact resolve b1e75 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e77 : x ≠ (M.op y y) ∨ y = (M.op x (M.op y y)) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e74
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e74
          | exact resolve b1e74 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e78 : y = (M.op x (M.op y y)) ∨ x = (M.op y y) ∨ (M.op y y) = (k y x) := by
          first
          | (have i₁ := b1e73
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e73
          | exact resolve b1e73 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e73
        have b1e79 : (M.op y y) = (k y x) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b1e78
             have r₂ := b1e76
             grind)
          | exact resolve b1e78 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e389 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e71 x y
             grind)
          | exact superpose b1e71 b1e19
          | (have j1 := b1e71 x y
             grind)
          | exact resolve b1e19 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e395 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e71 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e396 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e389
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e389
          | exact resolve b1e389 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e389
        have b1e637 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e396
             have i₂ := b1e79
             grind)
          | exact superpose b1e79 b1e396
          | exact resolve b1e396 b1e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e396
        have b1e640 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
        clear b1e637
        have b1e649 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e640
             grind)
          | exact superpose b1e640 b1e19
          | exact resolve b1e19 b1e640
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e651 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e640
             grind)
          | exact superpose b1e640 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e640
             grind)
          | exact resolve b1e16 b1e640
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e652 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e640
             grind)
          | exact superpose b1e640 b1e15
          | exact resolve b1e15 b1e640
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e640
        have b1e653 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by grind
        clear b1e651
        have b1e654 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e652
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e652
          | exact resolve b1e652 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e652
        have b1e655 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e653
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e653
          | exact resolve b1e653 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e653
        have b1e656 : (σ x) ≠ (σ (M.op y y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e649
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e649
          | exact resolve b1e649 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e649
        have b1e658 : (σ x) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e654
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e654
          | exact resolve b1e654 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e654
        have b1e659 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e655
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e655
          | exact resolve b1e655 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e655
        have b1e660 : (σ x) = (σ (k y x)) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b1e659
             have r₂ := b1e658
             grind)
          | exact resolve b1e659 b1e658
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e658 b1e659
        have b1e725 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e660
             have i₂ := b1e79
             grind)
          | exact superpose b1e79 b1e660
          | exact resolve b1e660 b1e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79 b1e660
        have b1e755 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
        clear b1e725
        have b1e776 : x = (M.op y y) := by
          first
          | (have r₁ := b1e755
             have r₂ := b1e656
             grind)
          | exact resolve b1e755 b1e656
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e656 b1e755
        have b1e847 : y ≠ (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e76
             have i₂ := b1e776
             grind)
          | exact superpose b1e776 b1e76
          | exact resolve b1e76 b1e776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e2535 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e77
             have i₂ := b1e776
             grind)
          | exact superpose b1e776 b1e77
          | (have r₁ := b1e77
             have r₂ := b1e776
             grind)
          | exact resolve b1e77 b1e776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e2536 : y = (M.op x x) ∨ x = (k y x) := by grind
        clear b1e2535
        have b1e2537 : x = (k y x) := by
          first
          | (have r₁ := b1e2536
             have r₂ := b1e847
             grind)
          | exact resolve b1e2536 b1e847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e847 b1e2536
        have b1e2655 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e395 x y
             have i₂ := b1e2537
             grind)
          | exact superpose b1e2537 b1e395
          | (have j0 := b1e395 x y
             grind)
          | exact resolve b1e395 b1e2537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e395 b1e2537
        have b1e2659 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b1e2655
        have b1e2903 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e2659
             grind)
          | exact superpose b1e2659 b1e19
          | exact resolve b1e19 b1e2659
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2659
        have b1e2910 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e2903
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e2903
          | exact resolve b1e2903 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63 b1e2903
        have b1e2914 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e2910
             have i₂ := b1e776
             grind)
          | exact superpose b1e776 b1e2910
          | exact resolve b1e2910 b1e776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e776 b1e2910
        have b1e2915 : False := by grind
        exact b1e2915
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e56 (σ X1) (σ X0)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e23 X1 X0
             have i₂ := b2e56 (τ X1) X0
             grind)
          | exact superpose b2e56 b2e23
          | (have j1 := b2e56 (τ X1) X0
             grind)
          | exact resolve b2e23 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e56
        have b2e207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e76 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e76
          | exact resolve b2e76 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e232 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e207 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e207
          | (have j0 := b2e207 X0 X1
             grind)
          | exact resolve b2e207 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e207
        have b2e358 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e74 x y
             grind)
          | exact superpose b2e74 b2e19
          | (have j1 := b2e74 x y
             grind)
          | exact resolve b2e19 b2e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e364 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e74 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e358
             have i₂ := b2e232 y x
             grind)
          | exact superpose b2e232 b2e358
          | (have j1 := b2e232 (σ y) (σ x)
             grind)
          | (have r₁ := b2e358
             have r₂ := b2e232 y x
             grind)
          | exact resolve b2e358 b2e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e358
        have b2e544 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b2e543
        have b2e547 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e544
             grind)
          | exact superpose b2e544 b2e19
          | exact resolve b2e19 b2e544
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e549 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e16 (σ y) (σ x)
             have i₂ := b2e544
             grind)
          | exact superpose b2e544 b2e16
          | (have j0 := b2e16 (σ y) (σ x)
             grind)
          | (have r₁ := b2e16 (σ y) (σ x)
             have r₂ := b2e544
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e544
             grind)
          | exact resolve b2e16 b2e544
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e550 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e15 (σ y) (σ x)
             have i₂ := b2e544
             grind)
          | exact superpose b2e544 b2e15
          | exact resolve b2e15 b2e544
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e544
        have b2e551 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
        clear b2e549
        have b2e552 : (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e550
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e550
          | exact resolve b2e550 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e550
        have b2e553 : (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e551
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e551
          | exact resolve b2e551 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e551
        have b2e555 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b2e553
             have r₂ := b2e552
             grind)
          | exact resolve b2e553 b2e552
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e552 b2e553
        have b2e688 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e232 y x
             have i₂ := b2e555
             grind)
          | exact superpose b2e555 b2e232
          | (have j0 := b2e232 y x
             grind)
          | exact resolve b2e232 b2e555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e232 b2e555
        have b2e711 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b2e688
        have b2e732 : x = (M.op x y) := by
          first
          | (have r₁ := b2e711
             have r₂ := b2e547
             grind)
          | exact resolve b2e711 b2e547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e547 b2e711
        have b2e814 : x ≠ x ∨ (M.op y x) = (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e732
             grind)
          | exact superpose b2e732 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e732
             grind)
          | exact resolve b2e16 b2e732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e815 : (M.op y x) ≠ (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e732
             grind)
          | exact superpose b2e732 b2e15
          | exact resolve b2e15 b2e732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e816 : (M.op y x) = (M.op x x) ∨ x = (k y x) := by grind
        clear b2e814
        have b2e817 : x = (k y x) := by
          first
          | (have r₁ := b2e816
             have r₂ := b2e815
             grind)
          | exact resolve b2e816 b2e815
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e815 b2e816
        have b2e901 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e364 x y
             have i₂ := b2e817
             grind)
          | exact superpose b2e817 b2e364
          | (have j0 := b2e364 x y
             grind)
          | exact resolve b2e364 b2e817
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e364 b2e817
        have b2e905 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e901
        have b2e995 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e905
             grind)
          | exact superpose b2e905 b2e19
          | exact resolve b2e19 b2e905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e905
        have b2e1002 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e995
             have i₂ := b2e732
             grind)
          | exact superpose b2e732 b2e995
          | exact resolve b2e995 b2e732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e732 b2e995
        have b2e1003 : False := by grind
        exact b2e1003
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op y (M.op y x)) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op x y) ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
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
        have b3e39 : (M.op (M.op (σ y) (σ x)) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ x)) (σ y)) := by
          first
          | (have i₁ := b3e15 (M.op (σ y) (σ x)) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e41 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e40
        have b3e42 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e41
          | exact resolve b3e41 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e43 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e22
          | exact resolve b3e22 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : y ≠ y ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by
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
        have b3e48 : (M.op x y) = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e45
        have b3e50 : y = (k x y) := by
          first
          | (have r₁ := b3e48
             have r₂ := b3e23
             grind)
          | exact resolve b3e48 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e55 : (M.op (M.op (σ y) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ x)) (σ y)) := by
          first
          | (have i₁ := b3e17 (M.op (σ y) (σ x)) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e17
          | exact resolve b3e17 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X0 X1
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e63 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ x)) (σ y)) := by
          first
          | (have r₁ := b3e55
             have r₂ := b3e39
             grind)
          | exact resolve b3e55 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e55
        have b3e64 : (M.op (σ x) (σ y)) = (k (σ (k x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e63
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e63
          | exact resolve b3e63 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e65 : (M.op (σ x) (σ y)) = (σ (k (k x y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e64
             have i₂ := b3e18 (k x y) y
             grind)
          | exact superpose b3e18 b3e64
          | exact resolve b3e64 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e66 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e65
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e65
          | exact resolve b3e65 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e62 (σ X1) (σ X0)
             grind)
          | exact superpose b3e62 b3e18
          | (have j1 := b3e62 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e24 X1 X0
             have i₂ := b3e62 (τ X1) X0
             grind)
          | exact superpose b3e62 b3e24
          | (have j1 := b3e62 (τ X1) X0
             grind)
          | exact resolve b3e24 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e98 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k y y))) ∨ (σ x) = (σ (k y y)) ∨ (σ (k y y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e17 (σ y) (σ x)
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e17
          | exact resolve b3e17 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e100 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ (k y y))) ∨ (σ (k y y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e15
          | exact resolve b3e15 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e102 : (σ (k x y)) ≠ (M.op (σ x) (σ (k y y))) ∨ (σ (k y y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e100
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e100
          | exact resolve b3e100 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e100
        have b3e104 : (σ (k x y)) = (M.op (σ x) (σ (k y y))) ∨ (σ x) = (σ (k y y)) ∨ (σ (k y y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e98
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e98
          | exact resolve b3e98 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98
        have b3e105 : (σ y) ≠ (M.op (σ x) (σ (k y y))) ∨ (σ (k y y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e102
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e102
          | exact resolve b3e102 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102
        have b3e107 : (σ y) = (M.op (σ x) (σ (k y y))) ∨ (σ x) = (σ (k y y)) ∨ (σ (k y y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e104
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e104
          | exact resolve b3e104 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104
        have b3e108 : (σ y) ≠ (M.op (σ x) (σ (k y y))) ∨ (σ (k y y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e105
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e105
          | exact resolve b3e105 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105
        have b3e110 : (σ (k y y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ (k y y))) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e107
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e107
          | exact resolve b3e107 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e107
        have b3e111 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y y)) ∨ (σ (k y y)) = (σ (k y x)) := by
          first
          | (have r₁ := b3e110
             have r₂ := b3e108
             grind)
          | exact resolve b3e110 b3e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e108 b3e110
        have b3e125 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e43
          | exact resolve b3e43 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e155 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e125
             grind)
          | exact superpose b3e125 b3e19
          | exact resolve b3e19 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e157 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e125
             grind)
          | exact superpose b3e125 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | exact resolve b3e16 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e158 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (M.op (σ y) (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e125
             grind)
          | exact superpose b3e125 b3e15
          | exact resolve b3e15 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e159 : (σ (k x y)) ≠ (M.op (σ x) (M.op (σ y) (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e158
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e158
          | exact resolve b3e158 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e158
        have b3e160 : (σ (k x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e157
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e157
          | exact resolve b3e157 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157
        have b3e163 : (σ y) ≠ (M.op (σ x) (M.op (σ y) (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e159
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e159
          | exact resolve b3e159 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e159
        have b3e164 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e160
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e160
          | exact resolve b3e160 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e160
        have b3e166 : (σ y) ≠ (M.op (σ x) (M.op (σ y) (σ y))) ∨ (M.op (σ y) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e163
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e163
          | exact resolve b3e163 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e163
        have b3e167 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b3e164
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e164
          | exact resolve b3e164 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e164
        have b3e301 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e80 X0 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e80
          | exact resolve b3e80 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e324 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e301 X0 X1
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e301
          | (have j0 := b3e301 X0 X1
             grind)
          | exact resolve b3e301 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e301
        have b3e491 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e79 x y
             grind)
          | exact superpose b3e79 b3e19
          | (have j1 := b3e79 x y
             grind)
          | exact resolve b3e19 b3e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e501 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e79 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e504 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e491
             have i₂ := b3e125
             grind)
          | exact superpose b3e125 b3e491
          | exact resolve b3e491 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e491
        have b3e570 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ (k y y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e111
             grind)
          | exact superpose b3e111 b3e15
          | exact resolve b3e15 b3e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e572 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ (k y y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e570
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e570
          | exact resolve b3e570 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e570
        have b3e577 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ (k y y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e572
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e572
          | exact resolve b3e572 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e572
        have b3e581 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ (k y y)) = (σ (k y x)) := by
          first
          | (have r₁ := b3e577
             have r₂ := b3e111
             grind)
          | exact resolve b3e577 b3e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111 b3e577
        have b3e583 : (σ (k y y)) = (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e581
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e581
          | exact resolve b3e581 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e581
        have b3e778 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e504
             have i₂ := b3e324 y x
             grind)
          | exact superpose b3e324 b3e504
          | (have j1 := b3e324 y x
             grind)
          | (have r₁ := b3e504
             have r₂ := b3e324 y x
             grind)
          | exact resolve b3e504 b3e324
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e504
        have b3e779 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
        clear b3e778
        have b3e782 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e155
             have i₂ := b3e779
             grind)
          | exact superpose b3e779 b3e155
          | exact resolve b3e155 b3e779
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e783 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e79 y y
             have i₂ := b3e779
             grind)
          | exact superpose b3e779 b3e79
          | exact resolve b3e79 b3e779
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e790 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e779
             grind)
          | exact superpose b3e779 b3e15
          | exact resolve b3e15 b3e779
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e791 : (σ x) ≠ (σ (k x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e790
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e790
          | exact resolve b3e790 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e790
        have b3e797 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e791
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e791
          | exact resolve b3e791 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e791
        have b3e804 : (σ x) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e797
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e797
          | exact resolve b3e797 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e797
        have b3e807 : (σ x) = (σ (k y y)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b3e804
             have r₂ := b3e783
             grind)
          | exact resolve b3e804 b3e783
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e783 b3e804
        have b3e948 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e807
             grind)
          | exact superpose b3e807 b3e13
          | exact resolve b3e13 b3e807
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e807
        have b3e987 : x = (k y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e948
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e948
          | exact resolve b3e948 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e948
        have b3e1076 : x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e62 y y
             have i₂ := b3e987
             grind)
          | exact superpose b3e987 b3e62
          | (have j0 := b3e62 y x
             grind)
          | exact resolve b3e62 b3e987
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62 b3e987
        have b3e1852 : x ≠ x ∨ (M.op y x) = (M.op x x) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e1076
             grind)
          | exact superpose b3e1076 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e1076
             grind)
          | (have r₁ := b3e16 y y
             have r₂ := b3e1076
             grind)
          | exact resolve b3e16 b3e1076
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1853 : (M.op y x) ≠ (M.op x x) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e1076
             grind)
          | exact superpose b3e1076 b3e15
          | exact resolve b3e15 b3e1076
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1854 : (M.op y x) = (M.op x x) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
        clear b3e1852
        have b3e1855 : y ≠ (M.op x x) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e1853
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1853
          | exact resolve b3e1853 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1853
        have b3e1856 : y = (M.op x x) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e1854
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1854
          | exact resolve b3e1854 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1854
        have b3e1857 : x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b3e1856
             have r₂ := b3e1855
             grind)
          | exact resolve b3e1856 b3e1855
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1855 b3e1856
        have b3e1974 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e501 x y
             have i₂ := b3e1857
             grind)
          | exact superpose b3e1857 b3e501
          | (have j0 := b3e501 x y
             grind)
          | exact resolve b3e501 b3e1857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e501 b3e1857
        have b3e1978 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
        clear b3e1974
        have b3e1982 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e1978
             have i₂ := b3e125
             grind)
          | exact superpose b3e125 b3e1978
          | exact resolve b3e1978 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e125 b3e1978
        have b3e4251 : (σ y) ≠ (σ (k y y)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by grind
        clear b3e583
        have b3e16252 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e155
             have i₂ := b3e1982
             grind)
          | exact superpose b3e1982 b3e155
          | exact resolve b3e155 b3e1982
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e155 b3e1982
        have b3e16598 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e16252
             have i₂ := b3e1076
             grind)
          | exact superpose b3e1076 b3e16252
          | exact resolve b3e16252 b3e1076
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1076 b3e16252
        have b3e16599 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
        clear b3e16598
        have b3e16600 : x = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e16599
        have b3e18584 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e166
             have i₂ := b3e779
             grind)
          | exact superpose b3e779 b3e166
          | exact resolve b3e166 b3e779
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e166
        have b3e69849 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e167
             have i₂ := b3e779
             grind)
          | exact superpose b3e779 b3e167
          | (have r₁ := b3e167
             have r₂ := b3e779
             grind)
          | exact resolve b3e167 b3e779
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e167 b3e779
        have b3e69851 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b3e69849
        have b3e69854 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b3e69851
             have r₂ := b3e18584
             grind)
          | exact resolve b3e69851 b3e18584
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18584 b3e69851
        have b3e69872 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e324 y x
             have i₂ := b3e69854
             grind)
          | exact superpose b3e69854 b3e324
          | (have j0 := b3e324 y x
             grind)
          | exact resolve b3e324 b3e69854
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e324 b3e69854
        have b3e69982 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b3e69872
        have b3e70051 : x = (M.op x y) := by
          first
          | (have r₁ := b3e69982
             have r₂ := b3e782
             grind)
          | exact resolve b3e69982 b3e782
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e782 b3e69982
        have b3e70497 : x ≠ (M.op y y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e70051
             grind)
          | exact superpose b3e70051 b3e23
          | exact resolve b3e23 b3e70051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e70502 : x ≠ x ∨ (M.op y x) = (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e70051
             grind)
          | exact superpose b3e70051 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e70051
             grind)
          | exact resolve b3e16 b3e70051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70503 : (M.op y x) ≠ (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e70051
             grind)
          | exact superpose b3e70051 b3e15
          | exact resolve b3e15 b3e70051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70051
        have b3e70504 : (M.op y x) = (M.op x x) ∨ x = (k y x) := by grind
        clear b3e70502
        have b3e70506 : y ≠ (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e70503
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e70503
          | exact resolve b3e70503 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70503
        have b3e70507 : y = (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e70504
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e70504
          | exact resolve b3e70504 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70504
        have b3e70509 : x = (k y x) := by
          first
          | (have r₁ := b3e70507
             have r₂ := b3e70506
             grind)
          | exact resolve b3e70507 b3e70506
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70506 b3e70507
        have b3e70980 : x ≠ x ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e70497
             have i₂ := b3e16600
             grind)
          | exact superpose b3e16600 b3e70497
          | (have r₁ := b3e70497
             have r₂ := b3e16600
             grind)
          | exact resolve b3e70497 b3e16600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e16600
        have b3e70981 : y = (M.op y y) := by grind
        clear b3e70980
        have b3e71936 : x ≠ y := by
          first
          | (have i₁ := b3e70497
             have i₂ := b3e70981
             grind)
          | exact superpose b3e70981 b3e70497
          | exact resolve b3e70497 b3e70981
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70497
        have b3e71938 : y ≠ (M.op y y) ∨ y = (k y y) := by
          first
          | (have i₁ := b3e15 y y
             have i₂ := b3e70981
             grind)
          | exact superpose b3e70981 b3e15
          | exact resolve b3e15 b3e70981
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e71940 : y = (k y y) := by
          first
          | (have r₁ := b3e71938
             have r₂ := b3e70981
             grind)
          | exact resolve b3e71938 b3e70981
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70981 b3e71938
        have b3e72811 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e4251
             have i₂ := b3e71940
             grind)
          | exact superpose b3e71940 b3e4251
          | exact resolve b3e4251 b3e71940
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4251 b3e71940
        have b3e72889 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
        clear b3e72811
        have b3e72894 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e72889
             have i₂ := b3e70509
             grind)
          | exact superpose b3e70509 b3e72889
          | exact resolve b3e72889 b3e70509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70509 b3e72889
        have b3e72895 : (σ x) = (σ y) := by grind
        clear b3e72894
        have b3e73043 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e72895
             grind)
          | exact superpose b3e72895 b3e13
          | exact resolve b3e13 b3e72895
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72895
        have b3e73210 : x = y := by
          first
          | (have i₁ := b3e73043
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e73043
          | exact resolve b3e73043 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73043
        have b3e73215 : False := by grind
        exact b3e73215
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e55 (σ X1) (σ X0)
               grind)
            | exact superpose b4e55 b4e19
            | (have j1 := b4e55 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X1 X0
               have i₂ := b4e55 (τ X1) X0
               grind)
            | exact superpose b4e55 b4e27
            | (have j1 := b4e55 (τ X1) X0
               grind)
            | exact resolve b4e27 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e55
          have b4e214 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e69 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e69
            | exact resolve b4e69 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e239 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e214 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e214
            | (have j0 := b4e214 X0 X1
               grind)
            | exact resolve b4e214 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214
          have b4e365 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e68 x y
               grind)
            | exact superpose b4e68 b4e20
            | (have j1 := b4e68 x y
               grind)
            | exact resolve b4e20 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e371 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e546 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e365
               have i₂ := b4e239 y x
               grind)
            | exact superpose b4e239 b4e365
            | (have j1 := b4e239 (σ y) (σ x)
               grind)
            | (have r₁ := b4e365
               have r₂ := b4e239 y x
               grind)
            | exact resolve b4e365 b4e239
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e365
          have b4e547 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e546
          have b4e551 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e547
               grind)
            | exact superpose b4e547 b4e20
            | exact resolve b4e20 b4e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e553 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e547
               grind)
            | exact superpose b4e547 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e547
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e547
               grind)
            | exact resolve b4e17 b4e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e554 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e547
               grind)
            | exact superpose b4e547 b4e16
            | exact resolve b4e16 b4e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e547
          have b4e555 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e553
          have b4e556 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e554
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e554
            | exact resolve b4e554 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e554
          have b4e557 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e555
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e555
            | exact resolve b4e555 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e555
          have b4e559 : (σ x) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e556
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e556
            | exact resolve b4e556 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e556
          have b4e560 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e557
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e557
            | exact resolve b4e557 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e557
          have b4e561 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e560
               have r₂ := b4e559
               grind)
            | exact resolve b4e560 b4e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e559 b4e560
          have b4e629 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e239 y x
               have i₂ := b4e561
               grind)
            | exact superpose b4e561 b4e239
            | (have j0 := b4e239 y x
               grind)
            | exact resolve b4e239 b4e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e239 b4e561
          have b4e652 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b4e629
          have b4e673 : x = (M.op x y) := by
            first
            | (have r₁ := b4e652
               have r₂ := b4e551
               grind)
            | exact resolve b4e652 b4e551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e551 b4e652
          have b4e745 : x ≠ x ∨ (M.op y x) = (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e673
               grind)
            | exact superpose b4e673 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e673
               grind)
            | exact resolve b4e17 b4e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e746 : (M.op y x) ≠ (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e673
               grind)
            | exact superpose b4e673 b4e16
            | exact resolve b4e16 b4e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e747 : (M.op y x) = (M.op x x) ∨ x = (k y x) := by grind
          clear b4e745
          have b4e748 : y ≠ (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e746
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e746
            | exact resolve b4e746 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e746
          have b4e749 : y = (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e747
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e747
            | exact resolve b4e747 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e747
          have b4e750 : x = (k y x) := by
            first
            | (have r₁ := b4e749
               have r₂ := b4e748
               grind)
            | exact resolve b4e749 b4e748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e748 b4e749
          have b4e910 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e371 x y
               have i₂ := b4e750
               grind)
            | exact superpose b4e750 b4e371
            | (have j0 := b4e371 x y
               grind)
            | exact resolve b4e371 b4e750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e371 b4e750
          have b4e914 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e910
          have b4e1005 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e914
               grind)
            | exact superpose b4e914 b4e20
            | exact resolve b4e20 b4e914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e914
          have b4e1012 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e1005
               have i₂ := b4e673
               grind)
            | exact superpose b4e673 b4e1005
            | exact resolve b4e1005 b4e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e673 b4e1005
          have b4e1013 : False := by grind
          exact b4e1013
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op y (M.op y x)) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op x y) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : y ≠ y ∨ (M.op x y) = (M.op y y) ∨ y = (k x y) := by
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
          have b5e42 : (M.op x y) = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e41
          have b5e43 : y = (k x y) := by
            first
            | (have r₁ := b5e42
               have r₂ := b5e25
               grind)
            | exact resolve b5e42 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e42
          have b5e48 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b5e48
          have b5e52 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e24
               grind)
            | exact resolve b5e49 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e53 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e52
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e52
            | exact resolve b5e52 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e54 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e53
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e53
            | exact resolve b5e53 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e53
          have b5e55 : False := by grind
          exact b5e55
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e38 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e39 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e38
        have b6e40 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e39
          | exact resolve b6e39 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X1
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e64 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e64 (σ X1) (σ X0)
             grind)
          | exact superpose b6e64 b6e18
          | (have j1 := b6e64 (σ X1) (σ X0)
             grind)
          | exact resolve b6e18 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e84 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e23 X1 X0
             have i₂ := b6e64 (τ X1) X0
             grind)
          | exact superpose b6e64 b6e23
          | (have j1 := b6e64 (τ X1) X0
             grind)
          | exact resolve b6e23 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e64
        have b6e260 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e84 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e84
          | exact resolve b6e84 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e260 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e260
          | (have j0 := b6e260 X0 X1
             grind)
          | exact resolve b6e260 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e260
        have b6e417 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e82 x y
             grind)
          | exact superpose b6e82 b6e19
          | (have j1 := b6e82 x y
             grind)
          | exact resolve b6e19 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e427 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e82 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e417
             have i₂ := b6e285 y x
             grind)
          | exact superpose b6e285 b6e417
          | (have j1 := b6e285 (σ y) (σ x)
             grind)
          | (have r₁ := b6e417
             have r₂ := b6e285 y x
             grind)
          | exact resolve b6e417 b6e285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e417
        have b6e854 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b6e853
        have b6e861 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e854
             grind)
          | exact superpose b6e854 b6e19
          | exact resolve b6e19 b6e854
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e863 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e854
             grind)
          | exact superpose b6e854 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e854
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e854
             grind)
          | exact resolve b6e16 b6e854
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e864 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e854
             grind)
          | exact superpose b6e854 b6e15
          | exact resolve b6e15 b6e854
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e854
        have b6e865 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
        clear b6e863
        have b6e866 : (σ (k x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e864
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e864
          | exact resolve b6e864 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e864
        have b6e867 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e865
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e865
          | exact resolve b6e865 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e865
        have b6e873 : (σ x) = (σ (k y x)) ∨ (σ (k x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e866
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e866
          | exact resolve b6e866 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e866
        have b6e874 : (σ x) = (σ (k y x)) ∨ (σ (k x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e867
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e867
          | exact resolve b6e867 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e867
        have b6e875 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e874
             have r₂ := b6e873
             grind)
          | exact resolve b6e874 b6e873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e873 b6e874
        have b6e1026 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e285 y x
             have i₂ := b6e875
             grind)
          | exact superpose b6e875 b6e285
          | (have j0 := b6e285 y x
             grind)
          | exact resolve b6e285 b6e875
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e285 b6e875
        have b6e1052 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b6e1026
        have b6e1073 : x = (M.op x y) := by
          first
          | (have r₁ := b6e1052
             have r₂ := b6e861
             grind)
          | exact resolve b6e1052 b6e861
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e861 b6e1052
        have b6e1163 : x ≠ x ∨ (M.op y x) = (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e1073
             grind)
          | exact superpose b6e1073 b6e16
          | (have j0 := b6e16 y x
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e1073
             grind)
          | exact resolve b6e16 b6e1073
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1164 : (M.op y x) ≠ (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e1073
             grind)
          | exact superpose b6e1073 b6e15
          | exact resolve b6e15 b6e1073
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1165 : (M.op y x) = (M.op x x) ∨ x = (k y x) := by grind
        clear b6e1163
        have b6e1166 : x = (k y x) := by
          first
          | (have r₁ := b6e1165
             have r₂ := b6e1164
             grind)
          | exact resolve b6e1165 b6e1164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1164 b6e1165
        have b6e1261 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e427 x y
             have i₂ := b6e1166
             grind)
          | exact superpose b6e1166 b6e427
          | (have j0 := b6e427 x y
             grind)
          | exact resolve b6e427 b6e1166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e427 b6e1166
        have b6e1265 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b6e1261
        have b6e1381 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e1265
             grind)
          | exact superpose b6e1265 b6e19
          | exact resolve b6e19 b6e1265
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1265
        have b6e1396 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b6e1381
             have i₂ := b6e1073
             grind)
          | exact superpose b6e1073 b6e1381
          | exact resolve b6e1381 b6e1073
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1073 b6e1381
        have b6e1397 : False := by grind
        exact b6e1397
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e42 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e43 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e25
               grind)
            | exact resolve b7e42 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e42
          have b7e44 : (σ y) = (σ (k x y)) := by
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
          have b7e47 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e14
            | exact resolve b7e14 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : y = (k x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e47
            | exact resolve b7e47 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X0 X1
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e57 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e64 : y = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e57 x y
               grind)
            | exact superpose b7e57 b7e48
            | (have j1 := b7e57 x y
               grind)
            | exact resolve b7e48 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e57
          have b7e66 : y = (M.op y x) := by grind
          clear b7e64
          have b7e69 : False := by grind
          exact b7e69
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e54 (σ X1) (σ X0)
               grind)
            | exact superpose b8e54 b8e19
            | (have j1 := b8e54 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e72 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e54 (τ X1) X0
               grind)
            | exact superpose b8e54 b8e25
            | (have j1 := b8e54 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e54
          have b8e173 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e72 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e72
            | exact resolve b8e72 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
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
          have b8e313 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e70 x y
               grind)
            | exact superpose b8e70 b8e20
            | (have j1 := b8e70 x y
               grind)
            | exact resolve b8e20 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e319 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e70 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e546 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e313
               have i₂ := b8e196 y x
               grind)
            | exact superpose b8e196 b8e313
            | (have j1 := b8e196 (σ y) (σ x)
               grind)
            | (have r₁ := b8e313
               have r₂ := b8e196 y x
               grind)
            | exact resolve b8e313 b8e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e313
          have b8e547 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e546
          have b8e550 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e547
               grind)
            | exact superpose b8e547 b8e20
            | exact resolve b8e20 b8e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e552 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e547
               grind)
            | exact superpose b8e547 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e547
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e547
               grind)
            | exact resolve b8e17 b8e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e553 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e547
               grind)
            | exact superpose b8e547 b8e16
            | exact resolve b8e16 b8e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e547
          have b8e554 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e552
          have b8e555 : (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e553
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e553
            | exact resolve b8e553 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e553
          have b8e556 : (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e554
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e554
            | exact resolve b8e554 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e554
          have b8e558 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e556
               have r₂ := b8e555
               grind)
            | exact resolve b8e556 b8e555
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e555 b8e556
          have b8e693 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e196 y x
               have i₂ := b8e558
               grind)
            | exact superpose b8e558 b8e196
            | (have j0 := b8e196 y x
               grind)
            | exact resolve b8e196 b8e558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e196 b8e558
          have b8e717 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b8e693
          have b8e738 : x = (M.op x y) := by
            first
            | (have r₁ := b8e717
               have r₂ := b8e550
               grind)
            | exact resolve b8e717 b8e550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e550 b8e717
          have b8e820 : x ≠ x ∨ (M.op y x) = (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e738
               grind)
            | exact superpose b8e738 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e738
               grind)
            | exact resolve b8e17 b8e738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e821 : (M.op y x) ≠ (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e738
               grind)
            | exact superpose b8e738 b8e16
            | exact resolve b8e16 b8e738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e822 : (M.op y x) = (M.op x x) ∨ x = (k y x) := by grind
          clear b8e820
          have b8e823 : x = (k y x) := by
            first
            | (have r₁ := b8e822
               have r₂ := b8e821
               grind)
            | exact resolve b8e822 b8e821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e821 b8e822
          have b8e908 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e319 x y
               have i₂ := b8e823
               grind)
            | exact superpose b8e823 b8e319
            | (have j0 := b8e319 x y
               grind)
            | exact resolve b8e319 b8e823
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319 b8e823
          have b8e912 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e908
          have b8e1003 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e912
               grind)
            | exact superpose b8e912 b8e20
            | exact resolve b8e20 b8e912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e912
          have b8e1010 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e1003
               have i₂ := b8e738
               grind)
            | exact superpose b8e738 b8e1003
            | exact resolve b8e1003 b8e738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e738 b8e1003
          have b8e1011 : False := by grind
          exact b8e1011

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_y_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
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
      have b0e30 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
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
      have b0e32 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e30
      have b0e33 : (M.op x y) = (k x y) := by grind
      clear b0e29
      have b0e36 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e32
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e32
        | exact resolve b0e32 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e38 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e36
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e36
        | exact resolve b0e36 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e36
      have b0e40 : False := by grind
      exact b0e40
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op y x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | (have r₁ := b1e15 y x
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 y x
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | (have r₁ := b1e15 y x
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : (M.op y x) = (k y x) := by grind
        clear b1e28
        have b1e31 : (M.op y x) = (k x y) := by grind
        clear b1e27
        have b1e36 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e37 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e36
        have b1e38 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e37
             have r₂ := b1e23
             grind)
          | exact resolve b1e37 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e39 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e38
          | exact resolve b1e38 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e40 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e39
          | exact resolve b1e39 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e39
        have b1e43 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
        have b1e89 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e43 x y
             grind)
          | (have i₁ := b1e23
             have i₂ := b1e43 y x
             grind)
          | exact superpose b1e43 b1e23
          | (have j1 := b1e43 x y
             grind)
          | exact resolve b1e23 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e100 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b1e89
             have r₂ := b1e22
             grind)
          | exact resolve b1e89 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89
        have b1e110 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e100
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e100
          | exact resolve b1e100 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e100
        have b1e112 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b1e110
             have r₂ := b1e24
             grind)
          | exact resolve b1e110 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e110
        have b1e116 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e112
             grind)
          | exact superpose b1e112 b1e23
          | exact resolve b1e23 b1e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e118 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e112
             grind)
          | exact superpose b1e112 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e112
             grind)
          | exact resolve b1e16 b1e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112
        have b1e121 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b1e118
        have b1e124 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e121
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e121
          | exact resolve b1e121 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121
        have b1e126 : (σ x) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b1e124
             have r₂ := b1e116
             grind)
          | exact resolve b1e124 b1e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124
        have b1e127 : (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b1e126
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e126
          | exact resolve b1e126 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126
        have b1e128 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e127
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e127
          | exact resolve b1e127 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e127
        have b1e129 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e128
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e128
          | exact resolve b1e128 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e128
        have b1e130 : False := by grind
        exact b1e130
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : (M.op y x) = (k y x) := by grind
        clear b2e39
        have b2e42 : (M.op y x) = (k x y) := by grind
        clear b2e38
        have b2e56 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e56 y x
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e56 x y
             grind)
          | exact superpose b2e56 b2e21
          | (have j1 := b2e56 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e56 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e56 x y
             grind)
          | exact resolve b2e21 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e71 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e56 x y
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e56 y x
             grind)
          | exact superpose b2e56 b2e21
          | (have j1 := b2e56 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e56 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e56 x y
             grind)
          | exact resolve b2e21 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e79 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
        clear b2e71
        have b2e82 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
        clear b2e67
        have b2e86 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e79
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e79
          | exact resolve b2e79 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e91 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e82
             have r₂ := b2e22
             grind)
          | exact resolve b2e82 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e96 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e86
             have r₂ := b2e23
             grind)
          | exact resolve b2e86 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e98 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e91
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e91
          | exact resolve b2e91 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e91
        have b2e102 : (σ x) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e96
             grind)
          | exact superpose b2e96 b2e23
          | exact resolve b2e23 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
        have b2e104 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b2e16 (σ y) (σ x)
             have i₂ := b2e96
             grind)
          | exact superpose b2e96 b2e16
          | (have j0 := b2e16 (σ y) (σ x)
             grind)
          | (have r₁ := b2e16 (σ y) (σ x)
             have r₂ := b2e96
             grind)
          | exact resolve b2e16 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96
        have b2e107 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b2e104
        have b2e110 : (σ x) = (σ (M.op y x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b2e107
             have i₂ := b2e98
             grind)
          | exact superpose b2e98 b2e107
          | exact resolve b2e107 b2e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98 b2e107
        have b2e112 : (σ x) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b2e110
             have r₂ := b2e102
             grind)
          | exact resolve b2e110 b2e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e110
        have b2e113 : (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b2e112
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e112
          | exact resolve b2e112 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e112
        have b2e114 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e113
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e113
          | exact resolve b2e113 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e113
        have b2e115 : False := by grind
        exact b2e115
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x y) ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : y ≠ (M.op x y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | (have r₁ := b3e15 (σ y) (σ x)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ y) (σ x)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | (have r₁ := b3e15 (σ y) (σ x)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
        clear b3e40
        have b3e43 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e39
        have b3e44 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e42
          | exact resolve b3e42 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e45 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e43
          | exact resolve b3e43 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e46 : (σ (k y x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e45
             have i₂ := b3e44
             grind)
          | exact superpose b3e44 b3e45
          | exact resolve b3e45 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e45
        have b3e57 : y ≠ y ∨ y = (M.op x y) ∨ y = (k x y) := by
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
        have b3e58 : y = (M.op x y) ∨ y = (k x y) := by grind
        clear b3e57
        have b3e59 : y = (k x y) := by
          first
          | (have r₁ := b3e58
             have r₂ := b3e23
             grind)
          | exact resolve b3e58 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e72 : (k x y) = (τ (σ (k y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e46
             grind)
          | exact superpose b3e46 b3e13
          | exact resolve b3e13 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e73 : (k y x) = (k x y) := by
          first
          | (have i₁ := b3e72
             have i₂ := b3e13 (k y x)
             grind)
          | exact superpose b3e13 b3e72
          | exact resolve b3e72 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e76 : y = (k y x) := by
          first
          | (have i₁ := b3e73
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e73
          | exact resolve b3e73 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e73
        have b3e87 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b3e17 y x
             have i₂ := b3e76
             grind)
          | exact superpose b3e76 b3e17
          | (have j0 := b3e17 y x
             grind)
          | exact resolve b3e17 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e88 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
          first
          | (have r₁ := b3e87
             have r₂ := b3e23
             grind)
          | exact resolve b3e87 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e90 : y = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e88
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e88
          | exact resolve b3e88 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88
        have b3e92 : x = (M.op x y) := by
          first
          | (have r₁ := b3e90
             have r₂ := b3e23
             grind)
          | exact resolve b3e90 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e128 : x ≠ y := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e92
             grind)
          | exact superpose b3e92 b3e23
          | exact resolve b3e23 b3e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e129 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e92
             grind)
          | exact superpose b3e92 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e92
             grind)
          | exact resolve b3e16 b3e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e132 : x = (M.op y x) ∨ x = (k y x) := by grind
        clear b3e129
        have b3e135 : x = y ∨ x = (k y x) := by
          first
          | (have i₁ := b3e132
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e132
          | exact resolve b3e132 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132
        have b3e136 : x = (k y x) := by
          first
          | (have r₁ := b3e135
             have r₂ := b3e128
             grind)
          | exact resolve b3e135 b3e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135
        have b3e137 : x = y := by
          first
          | (have i₁ := b3e136
             have i₂ := b3e76
             grind)
          | exact superpose b3e76 b3e136
          | exact resolve b3e136 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76 b3e136
        have b3e138 : False := by grind
        exact b3e138
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x y) ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : y ≠ (M.op x y) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e50 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
          have b4e76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X1) (σ X0)
               have i₂ := b4e50 X0 X1
               grind)
            | (have i₁ := b4e16 (σ X0) (σ X1)
               have i₂ := b4e50 X0 X1
               grind)
            | exact superpose b4e50 b4e16
            | (have j1 := b4e50 X0 X1
               grind)
            | (have r₁ := b4e16 (σ X1) (σ X0)
               have r₂ := b4e50 X0 X1
               grind)
            | (have r₁ := b4e16 (σ X0) (σ X1)
               have r₂ := b4e50 X0 X1
               grind)
            | exact resolve b4e16 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e78 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e50 x y
               grind)
            | (have i₁ := b4e25
               have i₂ := b4e50 y x
               grind)
            | exact superpose b4e50 b4e25
            | (have j1 := b4e50 x y
               grind)
            | exact resolve b4e25 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e85 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76
          have b4e89 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e78
               have r₂ := b4e24
               grind)
            | exact resolve b4e78 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e85 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e85
            | (have j0 := b4e85 X0 X1
               grind)
            | exact resolve b4e85 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85
          have b4e92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e91 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e335 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e89
               grind)
            | exact superpose b4e89 b4e20
            | exact resolve b4e20 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89
          have b4e389 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e92 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e92
            | exact resolve b4e92 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e408 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e92 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e414 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e389 X0 X1
               have i₂ := b4e28 X0 X1
               grind)
            | exact superpose b4e28 b4e389
            | (have j0 := b4e389 X0 X1
               grind)
            | exact resolve b4e389 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e389
          have b4e1353 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e414 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e414
            | exact resolve b4e414 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e414
          have b4e1529 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e335
               have i₂ := b4e1353 y x
               grind)
            | exact superpose b4e1353 b4e335
            | (have j1 := b4e1353 (σ y) (σ x)
               grind)
            | exact resolve b4e335 b4e1353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335
          have b4e1532 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e1529
          have b4e1540 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1532
               grind)
            | exact superpose b4e1532 b4e20
            | exact resolve b4e20 b4e1532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1541 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e1532
               grind)
            | exact superpose b4e1532 b4e25
            | exact resolve b4e25 b4e1532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e1546 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e1532
               grind)
            | exact superpose b4e1532 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e1532
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e1532
               grind)
            | exact resolve b4e17 b4e1532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1532
          have b4e1549 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e1546
          have b4e1552 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1549
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1549
            | exact resolve b4e1549 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1549
          have b4e1553 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e1552
               have r₂ := b4e1541
               grind)
            | exact resolve b4e1552 b4e1541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1541 b4e1552
          have b4e1554 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1553
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e1553
            | exact resolve b4e1553 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1553
          have b4e1777 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1554
               have i₂ := b4e1353 y x
               grind)
            | exact superpose b4e1353 b4e1554
            | (have j1 := b4e1353 y x
               grind)
            | exact resolve b4e1554 b4e1353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1353 b4e1554
          have b4e1820 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b4e1777
          have b4e1840 : x = (M.op x y) := by
            first
            | (have r₁ := b4e1820
               have r₂ := b4e1540
               grind)
            | exact resolve b4e1820 b4e1540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1540 b4e1820
          have b4e1968 : x ≠ y := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e1840
               grind)
            | exact superpose b4e1840 b4e26
            | exact resolve b4e26 b4e1840
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e1969 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e1840
               grind)
            | exact superpose b4e1840 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e1840
               grind)
            | exact resolve b4e17 b4e1840
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1972 : x = (M.op y x) ∨ x = (k y x) := by grind
          clear b4e1969
          have b4e1975 : x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b4e1972
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1972
            | exact resolve b4e1972 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1972
          have b4e1976 : x = (k y x) := by
            first
            | (have r₁ := b4e1975
               have r₂ := b4e1968
               grind)
            | exact resolve b4e1975 b4e1968
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1968 b4e1975
          have b4e2248 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e408 x y
               have i₂ := b4e1976
               grind)
            | exact superpose b4e1976 b4e408
            | (have j0 := b4e408 x y
               grind)
            | exact resolve b4e408 b4e1976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e408 b4e1976
          have b4e2251 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e2248
          have b4e2399 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e2251
               grind)
            | exact superpose b4e2251 b4e20
            | exact resolve b4e20 b4e2251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2251
          have b4e2412 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e2399
               have i₂ := b4e1840
               grind)
            | exact superpose b4e1840 b4e2399
            | exact resolve b4e2399 b4e1840
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1840 b4e2399
          have b4e2413 : False := by grind
          exact b4e2413
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ (M.op x y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : y ≠ y ∨ y = (M.op x y) ∨ y = (k x y) := by
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
          have b5e41 : y = (M.op x y) ∨ y = (k x y) := by grind
          clear b5e40
          have b5e42 : y = (k x y) := by
            first
            | (have r₁ := b5e41
               have r₂ := b5e25
               grind)
            | exact resolve b5e41 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e41
          have b5e45 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
          have b5e68 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e45 y x
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e45 x y
               grind)
            | exact superpose b5e45 b5e23
            | (have j1 := b5e45 y x
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e45 y x
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e45 x y
               grind)
            | exact resolve b5e23 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e83 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
          clear b5e68
          have b5e90 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e83
               have r₂ := b5e24
               grind)
            | exact resolve b5e83 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e95 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e90
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e90
            | exact resolve b5e90 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e90
          have b5e97 : False := by grind
          exact b5e97
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | (have r₁ := b6e15 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | (have r₁ := b6e15 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
        clear b6e39
        have b6e42 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e38
        have b6e43 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
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
        have b6e44 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e42
          | exact resolve b6e42 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e45 : (σ (k y x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e44
             have i₂ := b6e43
             grind)
          | exact superpose b6e43 b6e44
          | exact resolve b6e44 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e44
        have b6e58 : (k x y) = (τ (σ (k y x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e45
             grind)
          | exact superpose b6e45 b6e13
          | exact resolve b6e13 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e59 : (k y x) = (k x y) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e13 (k y x)
             grind)
          | exact superpose b6e13 b6e58
          | exact resolve b6e58 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e70 : (M.op y x) = (k y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e59
             grind)
          | exact superpose b6e59 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e71 : (M.op y x) = (k y x) ∨ y = (M.op y x) := by
          first
          | (have j1 := b6e15 y x
             grind)
          | (have r₁ := b6e70
             have r₂ := b6e15 x y
             grind)
          | (have r₁ := b6e70
             have r₂ := b6e15 y x
             grind)
          | exact resolve b6e70 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e73 : (M.op y x) = (k y x) := by
          first
          | (have r₁ := b6e71
             have r₂ := b6e21
             grind)
          | exact resolve b6e71 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e83 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e73
             grind)
          | exact superpose b6e73 b6e17
          | (have j0 := b6e17 y x
             grind)
          | exact resolve b6e17 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e84 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
        clear b6e83
        have b6e86 : x = (M.op x y) := by
          first
          | (have r₁ := b6e84
             have r₂ := b6e20
             grind)
          | exact resolve b6e84 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e124 : x ≠ (M.op y x) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e20
          | exact resolve b6e20 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e125 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e16
          | (have j0 := b6e16 y x
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e86
             grind)
          | exact resolve b6e16 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e128 : x = (M.op y x) ∨ x = (k y x) := by grind
        clear b6e125
        have b6e130 : x = (M.op y x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e128
             have i₂ := b6e73
             grind)
          | exact superpose b6e73 b6e128
          | exact resolve b6e128 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73 b6e128
        have b6e131 : x = (M.op y x) := by grind
        clear b6e130
        have b6e132 : False := by grind
        exact b6e132
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e41 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e42 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e25
               grind)
            | exact resolve b7e41 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e41
          have b7e43 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e42
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e42
            | exact resolve b7e42 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e43
               grind)
            | exact superpose b7e43 b7e14
            | exact resolve b7e14 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : y = (k x y) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e46
            | exact resolve b7e46 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e57 : y = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e58 : y = (M.op y x) ∨ (M.op x y) = (M.op y x) := by grind
          clear b7e57
          have b7e60 : (M.op x y) = (M.op y x) := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e22
               grind)
            | exact resolve b7e58 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e62 : False := by grind
          exact b7e62
        · have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op y x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b8e51 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e73 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e51 y x
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e51 x y
               grind)
            | exact superpose b8e51 b8e23
            | (have j1 := b8e51 y x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e51 y x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e51 x y
               grind)
            | exact resolve b8e23 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X1) (σ X0)
               have i₂ := b8e51 X0 X1
               grind)
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e51 X0 X1
               grind)
            | exact superpose b8e51 b8e16
            | (have j1 := b8e51 X0 X1
               grind)
            | (have r₁ := b8e16 (σ X1) (σ X0)
               have r₂ := b8e51 X0 X1
               grind)
            | (have r₁ := b8e16 (σ X0) (σ X1)
               have r₂ := b8e51 X0 X1
               grind)
            | exact resolve b8e16 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e51 x y
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e51 y x
               grind)
            | exact superpose b8e51 b8e23
            | (have j1 := b8e51 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e51 y x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e51 x y
               grind)
            | exact resolve b8e23 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e85 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e77
          have b8e86 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e88 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
          clear b8e73
          have b8e91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e86 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e86
            | (have j0 := b8e86 X0 X1
               grind)
            | exact resolve b8e86 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e91 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e95 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e88
               have r₂ := b8e24
               grind)
            | exact resolve b8e88 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e331 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e85
               grind)
            | exact superpose b8e85 b8e20
            | exact resolve b8e20 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e387 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e92 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e92
            | exact resolve b8e92 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e406 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e92 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e413 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e387 X0 X1
               have i₂ := b8e26 X0 X1
               grind)
            | exact superpose b8e26 b8e387
            | (have j0 := b8e387 X0 X1
               grind)
            | exact resolve b8e387 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e387
          have b8e1270 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e413 X0 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e413
            | exact resolve b8e413 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e413
          have b8e1567 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e331
               have i₂ := b8e1270 y x
               grind)
            | exact superpose b8e1270 b8e331
            | (have j1 := b8e1270 (σ y) (σ x)
               grind)
            | exact resolve b8e331 b8e1270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e331
          have b8e1570 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e1567
          have b8e1578 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e1570
               grind)
            | exact superpose b8e1570 b8e23
            | exact resolve b8e23 b8e1570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1579 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1570
               grind)
            | exact superpose b8e1570 b8e20
            | exact resolve b8e20 b8e1570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1584 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e1570
               grind)
            | exact superpose b8e1570 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e1570
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1570
               grind)
            | exact resolve b8e17 b8e1570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1570
          have b8e1587 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e1584
          have b8e1590 : (σ x) = (σ (k x y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1587
               have i₂ := b8e95
               grind)
            | exact superpose b8e95 b8e1587
            | exact resolve b8e1587 b8e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1587
          have b8e1591 : (σ x) ≠ (σ (k x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1578
               have i₂ := b8e95
               grind)
            | exact superpose b8e95 b8e1578
            | exact resolve b8e1578 b8e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95 b8e1578
          have b8e1594 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1590
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e1590
            | exact resolve b8e1590 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1590
          have b8e1595 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e1594
               have r₂ := b8e1591
               grind)
            | exact resolve b8e1594 b8e1591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1591 b8e1594
          have b8e1716 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1595
               have i₂ := b8e1270 y x
               grind)
            | exact superpose b8e1270 b8e1595
            | (have j1 := b8e1270 y x
               grind)
            | exact resolve b8e1595 b8e1270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1270 b8e1595
          have b8e1758 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b8e1716
          have b8e1778 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1758
               have r₂ := b8e1579
               grind)
            | exact resolve b8e1758 b8e1579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1579 b8e1758
          have b8e1893 : x ≠ (M.op y x) := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e1778
               grind)
            | exact superpose b8e1778 b8e21
            | exact resolve b8e21 b8e1778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1894 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e1778
               grind)
            | exact superpose b8e1778 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1778
               grind)
            | exact resolve b8e17 b8e1778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1897 : x = (k y x) ∨ x = (M.op y x) := by grind
          clear b8e1894
          have b8e2294 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e406 x y
               have i₂ := b8e1897
               grind)
            | exact superpose b8e1897 b8e406
            | (have j0 := b8e406 x y
               grind)
            | exact resolve b8e406 b8e1897
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e406 b8e1897
          have b8e2297 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
          clear b8e2294
          have b8e2304 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e2297
               have r₂ := b8e1893
               grind)
            | exact resolve b8e2297 b8e1893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1893 b8e2297
          have b8e2451 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2304
               grind)
            | exact superpose b8e2304 b8e20
            | exact resolve b8e20 b8e2304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2304
          have b8e2463 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e2451
               have i₂ := b8e1778
               grind)
            | exact superpose b8e1778 b8e2451
            | exact resolve b8e2451 b8e1778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1778 b8e2451
          have b8e2464 : False := by grind
          exact b8e2464

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,m(X,Y)) = m(Y,X) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pypxy_pyx_x_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b (M.op a b) ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b (M.op a b) = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b (M.op a b) = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y (M.op x y)) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e36 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      have b0e38 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e36 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e38 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e41 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e39 (σ X0)
           grind)
        | exact superpose b0e39 b0e17
        | exact resolve b0e17 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e41 X0
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e41
        | exact resolve b0e41 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e41
      have b0e51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X1 X0
           have j1 := b0e16 (M.op X0 X1) (k X1 X0)
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X1 (M.op X0 X1)) (M.op X1 X0)
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X1 X0) (M.op X1 (M.op X0 X1))
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e53 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e54 (τ X0) X1
           grind)
        | exact superpose b0e54 b0e23
        | (have j1 := b0e54 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e54 (σ X0) (σ X1)
           grind)
        | exact superpose b0e54 b0e17
        | (have j1 := b0e54 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e142 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e70 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e70
        | exact resolve b0e70 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e160 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e142 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e142
        | (have j0 := b0e142 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e142 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142
      have b0e499 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e71 x y
           grind)
        | exact superpose b0e71 b0e18
        | (have j1 := b0e71 x y
           grind)
        | exact resolve b0e18 b0e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71
      have b0e526 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e499
           have i₂ := b0e160 x y
           grind)
        | exact superpose b0e160 b0e499
        | (have j1 := b0e160 (σ x) (σ y)
           grind)
        | (have r₁ := b0e499
           have r₂ := b0e160 x y
           grind)
        | (have r₁ := b0e499
           have r₂ := b0e160 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e499
           have r₂ := b0e160 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e499 b0e160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e160 b0e499
      have b0e527 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e526
      have b0e535 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e12 x
           have i₂ := b0e527
           grind)
        | exact superpose b0e527 b0e12
        | exact resolve b0e12 b0e527
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e527
      have b0e566 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e535
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e535
        | exact resolve b0e535 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e535
      have b0e567 : x = y := by grind
      clear b0e566
      have b0e581 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e567
           grind)
        | exact superpose b0e567 b0e18
        | exact resolve b0e18 b0e567
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e567
      have b0e594 : False := by grind
      exact b0e594
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op y (M.op x y)) = (M.op y x) := by grind
        have b1e21 : (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = y := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e28 : (M.op y y) = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e20
          | exact resolve b1e20 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 y y
             have r₂ := b1e28
             grind)
          | exact resolve b1e15 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e51 : (M.op y y) = (k y y) := by grind
        clear b1e50
        have b1e58 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e24
        have b1e59 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e58
        have b1e62 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e59
          | exact resolve b1e59 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e63 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e62
          | exact resolve b1e62 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e62
        have b1e83 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e25
          | exact resolve b1e25 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e63
        have b1e88 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e83
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e83
          | exact resolve b1e83 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e83
        have b1e89 : False := by grind
        exact b1e89
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 (M.op X0 X1) (k X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X1 (M.op X0 X1)) (M.op X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X1 X0) (M.op X1 (M.op X0 X1))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e68 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e25 X0 X1
             have i₂ := b2e63 (τ X0) X1
             grind)
          | exact superpose b2e63 b2e25
          | (have j1 := b2e63 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b2e25 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e63 (σ X0) (σ X1)
             grind)
          | exact superpose b2e63 b2e18
          | (have j1 := b2e63 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e139 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e68 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e68
          | exact resolve b2e68 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e157 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e139 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e139
          | (have j0 := b2e139 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b2e139 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e139
        have b2e494 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e69 x y
             grind)
          | exact superpose b2e69 b2e19
          | (have j1 := b2e69 x y
             grind)
          | exact resolve b2e19 b2e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69
        have b2e510 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e494
             have r₂ := b2e22
             grind)
          | exact resolve b2e494 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e494
        have b2e521 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b2e510
             have i₂ := b2e157 x y
             grind)
          | exact superpose b2e157 b2e510
          | (have j1 := b2e157 x y
             grind)
          | (have r₁ := b2e510
             have r₂ := b2e157 x y
             grind)
          | (have r₁ := b2e510
             have r₂ := b2e157 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b2e510
             have r₂ := b2e157 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b2e510 b2e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e157 b2e510
        have b2e522 : x = y := by grind
        clear b2e521
        have b2e532 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e522
             grind)
          | exact superpose b2e522 b2e22
          | exact resolve b2e22 b2e522
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e522
        have b2e538 : False := by grind
        exact b2e538
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e34 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e35 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b3e34
        have b3e36 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e35
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e35
          | exact resolve b3e35 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e46 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b3e48 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e48 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e69 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e36
        have b3e72 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e69
             have i₂ := b3e49 y
             grind)
          | exact superpose b3e49 b3e69
          | exact resolve b3e69 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e69
        have b3e73 : False := by grind
        exact b3e73
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e46 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            grind
          have b4e48 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e48 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e49 (σ X0)
               grind)
            | exact superpose b4e49 b4e19
            | exact resolve b4e19 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e53 X0
               have i₂ := b4e49 X0
               grind)
            | exact superpose b4e49 b4e53
            | exact resolve b4e53 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e53
          have b4e110 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
          clear b4e58
          have b4e114 : False := by grind
          exact b4e114
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b6e62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 (M.op X0 X1) (k X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X1 (M.op X0 X1)) (M.op X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X1 X0) (M.op X1 (M.op X0 X1))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e66 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e66 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e25 X0 X1
             have i₂ := b6e67 (τ X0) X1
             grind)
          | exact superpose b6e67 b6e25
          | (have j1 := b6e67 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b6e25 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e67 (σ X0) (σ X1)
             grind)
          | exact superpose b6e67 b6e18
          | (have j1 := b6e67 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b6e18 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e142 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e70 (σ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e70
          | exact resolve b6e70 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e160 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e142 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e142
          | (have j0 := b6e142 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b6e142 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142
        have b6e497 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e71 x y
             grind)
          | exact superpose b6e71 b6e19
          | (have j1 := b6e71 x y
             grind)
          | exact resolve b6e19 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e497
             have i₂ := b6e160 x y
             grind)
          | exact superpose b6e160 b6e497
          | (have j1 := b6e160 (σ x) (σ y)
             grind)
          | (have r₁ := b6e497
             have r₂ := b6e160 x y
             grind)
          | (have r₁ := b6e497
             have r₂ := b6e160 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b6e497
             have r₂ := b6e160 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b6e497 b6e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e160 b6e497
        have b6e526 : (σ x) = (σ y) ∨ x = y := by grind
        clear b6e525
        have b6e528 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e526
             have r₂ := b6e21
             grind)
          | exact resolve b6e526 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e526
        have b6e560 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e528
             grind)
          | exact superpose b6e528 b6e13
          | exact resolve b6e13 b6e528
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e528
        have b6e591 : x = y := by
          first
          | (have i₁ := b6e560
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e560
          | exact resolve b6e560 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e560
        have b6e597 : False := by grind
        exact b6e597
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b8e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 (M.op X0 X1) (k X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X1 (M.op X0 X1)) (M.op X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op X1 (M.op X0 X1))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e69 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e63 (τ X0) X1
               grind)
            | exact superpose b8e63 b8e27
            | (have j1 := b8e63 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e27 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e63 (σ X0) (σ X1)
               grind)
            | exact superpose b8e63 b8e19
            | (have j1 := b8e63 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e138 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e69 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e69
            | exact resolve b8e69 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e156 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e138 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e138
            | (have j0 := b8e138 (σ (k X1 X0)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e138 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e493 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e70 x y
               grind)
            | exact superpose b8e70 b8e20
            | (have j1 := b8e70 x y
               grind)
            | exact resolve b8e20 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e509 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e493
               have r₂ := b8e24
               grind)
            | exact resolve b8e493 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e493
          have b8e520 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e509
               have i₂ := b8e156 x y
               grind)
            | exact superpose b8e156 b8e509
            | (have j1 := b8e156 x y
               grind)
            | (have r₁ := b8e509
               have r₂ := b8e156 x y
               grind)
            | (have r₁ := b8e509
               have r₂ := b8e156 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e509
               have r₂ := b8e156 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e509 b8e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156 b8e509
          have b8e521 : x = y := by grind
          clear b8e520
          have b8e523 : False := by grind
          exact b8e523

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,m(X,Y)) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pypxy_pyy_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b (M.op a b) ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b (M.op a b) = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b (M.op a b) = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y (M.op x y)) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op y (M.op x y)) = (M.op y y) := by grind
      have b0e20 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e30
      have b0e32 : (M.op x y) = (k x y) := by grind
      clear b0e29
      have b0e33 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e31
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e31
        | exact resolve b0e31 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e34 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e33
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e33
        | exact resolve b0e33 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e33
      have b0e35 : False := by grind
      exact b0e35
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : False := by grind
        exact b1e24
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op y (M.op x y)) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) := by
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
        have b2e39 : (M.op x y) = (k x y) := by grind
        clear b2e38
        have b2e54 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) (σ y)
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b2e54
        have b2e58 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e55
             have r₂ := b2e22
             grind)
          | exact resolve b2e55 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e61 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e58
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e58
          | exact resolve b2e58 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e62 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e61
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e61
          | exact resolve b2e61 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e61
        have b2e63 : False := by grind
        exact b2e63
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e20 : (M.op y (M.op x y)) ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op y y) ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : False := by grind
        exact b3e24
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e23 : (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : False := by grind
          exact b4e26
        · have b5e21 : (M.op y (M.op x y)) ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26 : False := by grind
          exact b5e26
    · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op y (M.op x y)) ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e39 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e38
        have b6e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e39
          | exact resolve b6e39 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e42 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e19
          | exact resolve b6e19 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e56 : (M.op y y) ≠ (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e20
          | (have j1 := b6e17 x y
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 x y
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
        clear b6e56
        have b6e60 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e57
             have r₂ := b6e21
             grind)
          | exact resolve b6e57 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e68 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e60
             grind)
          | exact superpose b6e60 b6e42
          | exact resolve b6e42 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e60
        have b6e69 : False := by grind
        exact b6e69
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26 : False := by grind
          exact b7e26
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op y (M.op x y)) ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e51 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) (σ y)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e52 : (M.op y y) ≠ (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b8e52
          have b8e54 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b8e51
          have b8e57 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e53
               have r₂ := b8e22
               grind)
            | exact resolve b8e53 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e58 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e54
               have r₂ := b8e24
               grind)
            | exact resolve b8e54 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e59 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e58
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e58
            | exact resolve b8e58 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e60 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e59
               have i₂ := b8e57
               grind)
            | exact superpose b8e57 b8e59
            | exact resolve b8e59 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57 b8e59
          have b8e61 : False := by grind
          exact b8e61
