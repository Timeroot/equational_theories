import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),m(Y,X)) = m(X,X) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxypyx_pxx_x_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) (M.op b a) ≠ M.op a a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b a)) (M.op a a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) (M.op b a) = M.op a a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b a)) (M.op a a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) (M.op b a) = M.op a a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b a)) (M.op a a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) (M.op y x)) (M.op x x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) (M.op (σ x) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e55 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      have b0e58 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e55 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e58 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e59 (σ X0)
           grind)
        | exact superpose b0e59 b0e17
        | exact resolve b0e17 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e63 X0
           have i₂ := b0e59 X0
           grind)
        | exact superpose b0e59 b0e63
        | exact resolve b0e63 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e63
      have b0e80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
           have r₂ := b0e16 (M.op (M.op X0 X1) (M.op X1 X0)) (M.op X0 X0)
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X0 X0) (M.op (M.op X0 X1) (M.op X1 X0))
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e80 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80
      have b0e84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e83 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e107 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e84 X1 (τ X0)
           grind)
        | exact superpose b0e84 b0e23
        | (have j1 := b0e84 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e108 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e84 (σ X1) (σ X0)
           grind)
        | exact superpose b0e84 b0e17
        | (have j1 := b0e84 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84
      have b0e224 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e107 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e107
        | exact resolve b0e107 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107
      have b0e240 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e224 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e224
        | (have j0 := b0e224 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e224 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e224
      have b0e611 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e108 x y
           grind)
        | exact superpose b0e108 b0e18
        | (have j1 := b0e108 x y
           grind)
        | exact resolve b0e18 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108
      have b0e667 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e611
           have i₂ := b0e240 x y
           grind)
        | exact superpose b0e240 b0e611
        | (have j1 := b0e240 (σ x) (σ y)
           grind)
        | (have r₁ := b0e611
           have r₂ := b0e240 x y
           grind)
        | (have r₁ := b0e611
           have r₂ := b0e240 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e611
           have r₂ := b0e240 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e611 b0e240
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e240 b0e611
      have b0e668 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e667
      have b0e682 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e668
           grind)
        | exact superpose b0e668 b0e12
        | exact resolve b0e12 b0e668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e668
      have b0e713 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e682
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e682
        | exact resolve b0e682 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e682
      have b0e714 : x = y := by grind
      clear b0e713
      have b0e773 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e714
           grind)
        | exact superpose b0e714 b0e18
        | exact resolve b0e18 b0e714
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e714
      have b0e792 : False := by grind
      exact b0e792
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b1e73 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b1e76 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e73 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e76 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e82 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e77 (σ X0)
             grind)
          | exact superpose b1e77 b1e18
          | exact resolve b1e18 b1e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e82 X0
             have i₂ := b1e77 X0
             grind)
          | exact superpose b1e77 b1e82
          | exact resolve b1e82 b1e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77 b1e82
        have b1e149 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e85 x
             grind)
          | exact superpose b1e85 b1e25
          | exact resolve b1e25 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e85
        have b1e157 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e149
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e149
          | exact resolve b1e149 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e149
        have b1e158 : False := by grind
        exact b1e158
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b2e63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
             have r₂ := b2e17 (M.op (M.op X0 X1) (M.op X1 X0)) (M.op X0 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X0 X0) (M.op (M.op X0 X1) (M.op X1 X0))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e66 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e72 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e25 X0 X1
             have i₂ := b2e67 X1 (τ X0)
             grind)
          | exact superpose b2e67 b2e25
          | (have j1 := b2e67 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b2e25 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e67 (σ X1) (σ X0)
             grind)
          | exact superpose b2e67 b2e18
          | (have j1 := b2e67 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e171 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e72 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e72
          | exact resolve b2e72 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72
        have b2e187 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e171 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e171
          | (have j0 := b2e171 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b2e171 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171
        have b2e504 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e73 x y
             grind)
          | exact superpose b2e73 b2e19
          | (have j1 := b2e73 x y
             grind)
          | exact resolve b2e19 b2e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e527 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e504
             have r₂ := b2e22
             grind)
          | exact resolve b2e504 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504
        have b2e539 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b2e527
             have i₂ := b2e187 x y
             grind)
          | exact superpose b2e187 b2e527
          | (have j1 := b2e187 x y
             grind)
          | (have r₁ := b2e527
             have r₂ := b2e187 x y
             grind)
          | (have r₁ := b2e527
             have r₂ := b2e187 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b2e527
             have r₂ := b2e187 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b2e527 b2e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187 b2e527
        have b2e540 : x = y := by grind
        clear b2e539
        have b2e545 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e540
             grind)
          | exact superpose b2e540 b2e22
          | exact resolve b2e22 b2e540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e540
        have b2e550 : False := by grind
        exact b2e550
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) (M.op (σ x) (σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e51 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e52 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b3e51
        have b3e53 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e52
          | exact resolve b3e52 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e61 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e53
        have b3e68 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b3e71 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e68 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e71 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e95 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e61
             have i₂ := b3e72 y
             grind)
          | exact superpose b3e72 b3e61
          | exact resolve b3e61 b3e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e72
        have b3e96 : False := by grind
        exact b3e96
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e67 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            grind
          have b4e70 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e67 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e70 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e71 (σ X0)
               grind)
            | exact superpose b4e71 b4e19
            | exact resolve b4e19 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e75 X0
               have i₂ := b4e71 X0
               grind)
            | exact superpose b4e71 b4e75
            | exact resolve b4e75 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71 b4e75
          have b4e114 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
          clear b4e84
          have b4e119 : False := by grind
          exact b4e119
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) (M.op (σ x) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e70 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
             have r₂ := b6e17 (M.op (M.op X0 X1) (M.op X1 X0)) (M.op X0 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X0 X0) (M.op (M.op X0 X1) (M.op X1 X0))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e70 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e74 (σ X1) (σ X0)
             grind)
          | exact superpose b6e74 b6e18
          | (have j1 := b6e74 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b6e18 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e83 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X1 X0
             have i₂ := b6e74 (τ X1) X0
             grind)
          | exact superpose b6e74 b6e24
          | (have j1 := b6e74 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
             grind)
          | exact resolve b6e24 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e74
        have b6e222 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e83 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e83
          | exact resolve b6e83 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e238 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e222 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e222
          | (have j0 := b6e222 (σ (k X0 X1)) (σ (M.op X1 X0))
             grind)
          | exact resolve b6e222 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e222
        have b6e569 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
        clear b6e82
        have b6e654 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e569
             have i₂ := b6e238 y x
             grind)
          | exact superpose b6e238 b6e569
          | (have j1 := b6e238 (σ x) (σ y)
             grind)
          | (have r₁ := b6e569
             have r₂ := b6e238 y x
             grind)
          | (have r₁ := b6e569
             have r₂ := b6e238 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b6e569
             have r₂ := b6e238 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b6e569 b6e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e238 b6e569
        have b6e655 : (σ x) = (σ y) ∨ x = y := by grind
        clear b6e654
        have b6e657 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e655
             have r₂ := b6e21
             grind)
          | exact resolve b6e655 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e655
        have b6e696 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e657
             grind)
          | exact superpose b6e657 b6e13
          | exact resolve b6e13 b6e657
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e657
        have b6e727 : x = y := by
          first
          | (have i₁ := b6e696
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e696
          | exact resolve b6e696 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e696
        have b6e735 : False := by grind
        exact b6e735
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
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X0)) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
               have r₂ := b8e18 (M.op (M.op X0 X1) (M.op X1 X0)) (M.op X0 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op (M.op X0 X1) (M.op X1 X0))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e91 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e92 (σ X1) (σ X0)
               grind)
            | exact superpose b8e92 b8e19
            | (have j1 := b8e92 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e92 (τ X1) X0
               grind)
            | exact superpose b8e92 b8e26
            | (have j1 := b8e92 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
               grind)
            | exact resolve b8e26 b8e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e92
          have b8e140 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e99 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e99
            | exact resolve b8e99 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e156 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e140 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e140
            | (have j0 := b8e140 (σ (k X0 X1)) (σ (M.op X1 X0))
               grind)
            | exact resolve b8e140 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e485 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e97 x y
               grind)
            | exact superpose b8e97 b8e20
            | (have j1 := b8e97 x y
               grind)
            | exact resolve b8e20 b8e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97
          have b8e508 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e485
               have r₂ := b8e24
               grind)
            | exact resolve b8e485 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e485
          have b8e519 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e508
               have i₂ := b8e156 y x
               grind)
            | exact superpose b8e156 b8e508
            | (have j1 := b8e156 x y
               grind)
            | (have r₁ := b8e508
               have r₂ := b8e156 y x
               grind)
            | (have r₁ := b8e508
               have r₂ := b8e156 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e508
               have r₂ := b8e156 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e508 b8e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156 b8e508
          have b8e520 : x = y := by grind
          clear b8e519
          have b8e522 : False := by grind
          exact b8e522

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),m(Y,Y)) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxypyy_pyx_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) (M.op b b) ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b b)) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) (M.op b b) = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b b)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) (M.op b b) = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b b)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) (M.op y y)) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x y) (M.op y y)) = (M.op y x) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e45 : (M.op y x) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
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
      have b0e46 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e47 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e46
      have b0e48 : (M.op x y) = (k x y) := by grind
      clear b0e45
      have b0e49 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e47
        | exact resolve b0e47 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e50 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e49
        | exact resolve b0e49 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e49
      have b0e51 : False := by grind
      exact b0e51
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op (M.op x y) (M.op y y)) = (M.op y x) := by grind
        have b1e21 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b1e41 : (M.op y x) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
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
        have b1e42 : (M.op x y) = (k x y) := by grind
        clear b1e41
        have b1e43 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e45 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e46 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e45
             have r₂ := b1e23
             grind)
          | exact resolve b1e45 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e45
        have b1e47 : (σ y) = (σ (k x y)) := by
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
        have b1e48 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e47
          | exact resolve b1e47 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e47
        have b1e49 : False := by grind
        exact b1e49
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op x y) (M.op y y)) = (M.op y x) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : (M.op y x) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
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
        have b2e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 (M.op X1 X1) (M.op X1 X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e58 (σ X1) (σ X0)
             grind)
          | exact superpose b2e58 b2e18
          | (have j1 := b2e58 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e407 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e76 x y
             grind)
          | exact superpose b2e76 b2e19
          | (have j1 := b2e76 x y
             grind)
          | exact resolve b2e19 b2e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e422 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e407
             have r₂ := b2e22
             grind)
          | exact resolve b2e407 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e407
        have b2e426 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e422
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e422
          | exact resolve b2e422 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e422
        have b2e427 : False := by grind
        exact b2e427
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op (M.op x y) (M.op y y)) ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op y x) ≠ (M.op y (M.op y y)) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b3e41 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e42 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e41
        have b3e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e42
          | exact resolve b3e42 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e45 : (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e24
          | exact resolve b3e24 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e43
        have b3e47 : y ≠ y ∨ (M.op y x) = (M.op y (M.op y y)) ∨ y = (k x y) := by
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
        have b3e50 : (M.op y x) = (M.op y (M.op y y)) ∨ y = (k x y) := by grind
        clear b3e47
        have b3e52 : y = (k x y) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e23
             grind)
          | exact resolve b3e50 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e50
        have b3e69 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e45
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e45
          | exact resolve b3e45 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e52
        have b3e70 : False := by grind
        exact b3e70
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
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op (M.op x y) (M.op y y)) ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y x) ≠ (M.op y (M.op y y)) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : y ≠ y ∨ (M.op y x) = (M.op y (M.op y y)) ∨ y = (k x y) := by
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
          have b5e51 : (M.op y x) = (M.op y (M.op y y)) ∨ y = (k x y) := by grind
          clear b5e50
          have b5e52 : y = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e25
               grind)
            | exact resolve b5e51 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e51
          have b5e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 (M.op X1 X1) (M.op X1 X1)
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e61 (σ X1) (σ X0)
               grind)
            | exact superpose b5e61 b5e19
            | (have j1 := b5e61 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e379 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e79 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e481 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e379 x y
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e379
            | (have j0 := b5e379 x y
               grind)
            | exact resolve b5e379 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e379
          have b5e485 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e481
          have b5e488 : False := by grind
          exact b5e488
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 (M.op X1 X1) (M.op X1 X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e75 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e58 y x
             grind)
          | exact superpose b6e58 b6e42
          | (have j1 := b6e58 y x
             grind)
          | exact resolve b6e42 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e58
        have b6e76 : y = (M.op x y) := by grind
        clear b6e75
        have b6e77 : False := by grind
        exact b6e77
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e62 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e63 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e62
          have b7e64 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e25
               grind)
            | exact resolve b7e63 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e63
          have b7e65 : (σ y) = (σ (k x y)) := by
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
          have b7e70 : (k x y) = (τ (σ y)) := by
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
          have b7e71 : y = (k x y) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e70
            | exact resolve b7e70 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e79 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X1 X0
               have i₂ := b7e18 X1 X0
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X0
               have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 (M.op X1 X1) (M.op X1 X1)
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e83 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e79 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e93 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e84 y x
               grind)
            | exact superpose b7e84 b7e71
            | (have j1 := b7e84 y x
               grind)
            | exact resolve b7e71 b7e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e84
          have b7e95 : y = (M.op x y) := by grind
          clear b7e93
          have b7e98 : False := by grind
          exact b7e98
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e73 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 (M.op X1 X1) (M.op X1 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e78 (σ X1) (σ X0)
               grind)
            | exact superpose b8e78 b8e19
            | (have j1 := b8e78 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e85 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e78 X1 (τ X0)
               grind)
            | exact superpose b8e78 b8e25
            | (have j1 := b8e78 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e78
          have b8e209 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e85 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e85
            | exact resolve b8e85 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e234 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e209 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e209
            | (have j0 := b8e209 X0 X1
               grind)
            | exact resolve b8e209 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209
          have b8e357 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e83 x y
               grind)
            | exact superpose b8e83 b8e20
            | (have j1 := b8e83 x y
               grind)
            | exact resolve b8e20 b8e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e372 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e357
               have r₂ := b8e24
               grind)
            | exact resolve b8e357 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e357
          have b8e377 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e372
               have i₂ := b8e234 x y
               grind)
            | exact superpose b8e234 b8e372
            | (have j1 := b8e234 x y
               grind)
            | (have r₁ := b8e372
               have r₂ := b8e234 x y
               grind)
            | exact resolve b8e372 b8e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e234 b8e372
          have b8e378 : y = (M.op x y) := by grind
          clear b8e377
          have b8e380 : False := by grind
          exact b8e380

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),m(Y,Y)) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxypyy_x_pyx_y_pyx_y_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) (M.op b b) ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b b)) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) (M.op b b) = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b b)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) (M.op b b) = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op b b)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) (M.op y y)) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op (M.op x y) (M.op y y)) := by grind
      have b0e20 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by grind
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
      have b0e29 : x ≠ x ∨ (k x y) = (M.op y x) := by
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
      have b0e30 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
      have b0e31 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
      clear b0e30
      have b0e32 : (k x y) = (M.op y x) := by grind
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
      have b0e49 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e53 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e49 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e53 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e61 : (σ y) ≠ (M.op (σ (M.op y x)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | exact resolve b0e14 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : (σ y) ≠ (M.op (σ (M.op y x)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e61
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e61
        | exact resolve b0e61 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e54 (σ X1) (σ X0)
           grind)
        | exact superpose b0e54 b0e17
        | (have j1 := b0e54 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e54 (τ X1) X0
           grind)
        | exact superpose b0e54 b0e21
        | (have j1 := b0e54 (τ X1) X0
           grind)
        | exact resolve b0e21 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e54
      have b0e234 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e66 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e66
        | exact resolve b0e66 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e234 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e234
        | (have j0 := b0e234 X0 X1
           grind)
        | exact resolve b0e234 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e234
      have b0e384 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e65 x y
           grind)
        | exact superpose b0e65 b0e18
        | (have j1 := b0e65 x y
           grind)
        | exact resolve b0e18 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e396 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e65 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e590 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e384
           have i₂ := b0e259 y x
           grind)
        | exact superpose b0e259 b0e384
        | (have j1 := b0e259 (σ y) (σ x)
           grind)
        | (have r₁ := b0e384
           have r₂ := b0e259 y x
           grind)
        | exact resolve b0e384 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e384
      have b0e591 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e590
      have b0e596 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e591
           grind)
        | exact superpose b0e591 b0e18
        | exact resolve b0e18 b0e591
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e599 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e591
           grind)
        | exact superpose b0e591 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e591
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e591
           grind)
        | exact resolve b0e15 b0e591
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e601 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
      clear b0e599
      have b0e605 : (σ y) = (M.op (σ (M.op y x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e601
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e601
        | exact resolve b0e601 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e601
      have b0e607 : (σ y) = (M.op (σ (M.op y x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e605
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e605
        | exact resolve b0e605 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e605
      have b0e508654 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e62
           have i₂ := b0e607
           grind)
        | exact superpose b0e607 b0e62
        | (have r₁ := b0e62
           have r₂ := b0e607
           grind)
        | exact resolve b0e62 b0e607
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62 b0e607
      have b0e508656 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
      clear b0e508654
      have b0e509292 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e591
           have i₂ := b0e508656
           grind)
        | exact superpose b0e508656 b0e591
        | exact resolve b0e591 b0e508656
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e591 b0e508656
      have b0e509343 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
      clear b0e509292
      have b0e509978 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e259 y x
           have i₂ := b0e509343
           grind)
        | exact superpose b0e509343 b0e259
        | (have j0 := b0e259 y x
           grind)
        | exact resolve b0e259 b0e509343
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e259 b0e509343
      have b0e510258 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
      clear b0e509978
      have b0e510318 : x = (M.op x y) := by
        first
        | (have r₁ := b0e510258
           have r₂ := b0e596
           grind)
        | exact resolve b0e510258 b0e596
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e596 b0e510258
      have b0e510938 : x ≠ x ∨ y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e510318
           grind)
        | exact superpose b0e510318 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e510318
           grind)
        | exact resolve b0e15 b0e510318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e510941 : y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by grind
      clear b0e510938
      have b0e512182 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e510941
           grind)
        | exact superpose b0e510941 b0e14
        | (have j0 := b0e14 y x
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e510941
           grind)
        | exact resolve b0e14 b0e510941
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e510941
      have b0e512199 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
      clear b0e512182
      have b0e512200 : x = (k y x) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e512199
           have i₂ := b0e510318
           grind)
        | exact superpose b0e510318 b0e512199
        | exact resolve b0e512199 b0e510318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e512199
      have b0e512201 : x = (k y x) := by grind
      clear b0e512200
      have b0e512848 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e396 x y
           have i₂ := b0e512201
           grind)
        | exact superpose b0e512201 b0e396
        | (have j0 := b0e396 x y
           grind)
        | exact resolve b0e396 b0e512201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e396 b0e512201
      have b0e513045 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear b0e512848
      have b0e514343 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e513045
           grind)
        | exact superpose b0e513045 b0e18
        | exact resolve b0e18 b0e513045
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e513045
      have b0e514360 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e514343
           have i₂ := b0e510318
           grind)
        | exact superpose b0e510318 b0e514343
        | exact resolve b0e514343 b0e510318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e510318 b0e514343
      have b0e514361 : False := by grind
      exact b0e514361
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op (M.op x y) (M.op y y)) := by grind
        have b1e21 : (σ x) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e37 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) (σ x)
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : x ≠ x ∨ (k x y) = (M.op y x) := by
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
        have b1e40 : (k x y) = (M.op y x) := by grind
        clear b1e39
        have b1e41 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e37
          | exact resolve b1e37 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e42 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e44 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e42
        have b1e45 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
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
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e46
          | exact resolve b1e46 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e46
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
        have b1e59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b1e63 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e70 : y ≠ (M.op y (M.op x x)) ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e15
          | (have j0 := b1e15 y x
             grind)
          | exact resolve b1e15 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e64 (σ X1) (σ X0)
             grind)
          | exact superpose b1e64 b1e18
          | (have j1 := b1e64 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e23 X1 X0
             have i₂ := b1e64 (τ X1) X0
             grind)
          | exact superpose b1e64 b1e23
          | (have j1 := b1e64 (τ X1) X0
             grind)
          | exact resolve b1e23 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e64
        have b1e264 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e76 X0 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e76
          | exact resolve b1e76 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e289 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e264 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e264
          | (have j0 := b1e264 X0 X1
             grind)
          | exact resolve b1e264 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e264
        have b1e418 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e75 x y
             grind)
          | exact superpose b1e75 b1e19
          | (have j1 := b1e75 x y
             grind)
          | exact resolve b1e19 b1e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e428 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e75 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e614 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e418
             have i₂ := b1e289 y x
             grind)
          | exact superpose b1e289 b1e418
          | (have j1 := b1e289 (σ y) (σ x)
             grind)
          | (have r₁ := b1e418
             have r₂ := b1e289 y x
             grind)
          | exact resolve b1e418 b1e289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e418
        have b1e615 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b1e614
        have b1e619 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e615
             grind)
          | exact superpose b1e615 b1e19
          | exact resolve b1e19 b1e615
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e622 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e615
             grind)
          | exact superpose b1e615 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e615
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e615
             grind)
          | exact resolve b1e16 b1e615
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e624 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
        clear b1e622
        have b1e627 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e624
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e624
          | exact resolve b1e624 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e624
        have b1e628 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e627
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e627
          | exact resolve b1e627 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e627
        have b1e104154 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e628
             grind)
          | exact superpose b1e628 b1e41
          | (have r₁ := b1e41
             have r₂ := b1e628
             grind)
          | exact resolve b1e41 b1e628
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e628
        have b1e104163 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b1e104154
        have b1e104632 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e615
             have i₂ := b1e104163
             grind)
          | exact superpose b1e104163 b1e615
          | exact resolve b1e615 b1e104163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e615 b1e104163
        have b1e104731 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b1e104632
        have b1e105356 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e289 y x
             have i₂ := b1e104731
             grind)
          | exact superpose b1e104731 b1e289
          | (have j0 := b1e289 y x
             grind)
          | exact resolve b1e289 b1e104731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e289 b1e104731
        have b1e105526 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b1e105356
        have b1e105586 : x = (M.op x y) := by
          first
          | (have r₁ := b1e105526
             have r₂ := b1e619
             grind)
          | exact resolve b1e105526 b1e619
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e619 b1e105526
        have b1e106166 : x ≠ x ∨ y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e105586
             grind)
          | exact superpose b1e105586 b1e16
          | (have j0 := b1e16 y x
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e105586
             grind)
          | exact resolve b1e16 b1e105586
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e106171 : y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by grind
        clear b1e106166
        have b1e106173 : y = (M.op y (M.op x x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e106171
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e106171
          | exact resolve b1e106171 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e106171
        have b1e107137 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e70
             have i₂ := b1e106173
             grind)
          | exact superpose b1e106173 b1e70
          | (have r₁ := b1e70
             have r₂ := b1e106173
             grind)
          | exact resolve b1e70 b1e106173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e106173
        have b1e107146 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
        clear b1e107137
        have b1e107147 : x = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e107146
             have i₂ := b1e105586
             grind)
          | exact superpose b1e105586 b1e107146
          | exact resolve b1e107146 b1e105586
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107146
        have b1e107148 : x = (k y x) := by grind
        clear b1e107147
        have b1e107650 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e428 x y
             have i₂ := b1e107148
             grind)
          | exact superpose b1e107148 b1e428
          | (have j0 := b1e428 x y
             grind)
          | exact resolve b1e428 b1e107148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e428 b1e107148
        have b1e107747 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b1e107650
        have b1e110247 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e107747
             grind)
          | exact superpose b1e107747 b1e19
          | exact resolve b1e19 b1e107747
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107747
        have b1e110266 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e110247
             have i₂ := b1e105586
             grind)
          | exact superpose b1e105586 b1e110247
          | exact resolve b1e110247 b1e105586
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105586 b1e110247
        have b1e110267 : False := by grind
        exact b1e110267
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e53 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e58 (σ X1) (σ X0)
             grind)
          | exact superpose b2e58 b2e18
          | (have j1 := b2e58 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e23 X1 X0
             have i₂ := b2e58 (τ X1) X0
             grind)
          | exact superpose b2e58 b2e23
          | (have j1 := b2e58 (τ X1) X0
             grind)
          | exact resolve b2e23 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e58
        have b2e219 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e79 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e79
          | exact resolve b2e79 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e244 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e219 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e219
          | (have j0 := b2e219 X0 X1
             grind)
          | exact resolve b2e219 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e219
        have b2e369 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e77 x y
             grind)
          | exact superpose b2e77 b2e19
          | (have j1 := b2e77 x y
             grind)
          | exact resolve b2e19 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e378 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e77 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e369
             have i₂ := b2e244 y x
             grind)
          | exact superpose b2e244 b2e369
          | (have j1 := b2e244 (σ y) (σ x)
             grind)
          | (have r₁ := b2e369
             have r₂ := b2e244 y x
             grind)
          | exact resolve b2e369 b2e244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e369
        have b2e544 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b2e543
        have b2e621 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e544
             grind)
          | exact superpose b2e544 b2e19
          | exact resolve b2e19 b2e544
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e624 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
        have b2e626 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
        clear b2e624
        have b2e629 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e626
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e626
          | exact resolve b2e626 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e626
        have b2e579302 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e15 (σ y) (σ x)
             have i₂ := b2e629
             grind)
          | exact superpose b2e629 b2e15
          | (have j0 := b2e15 (σ y) (σ x)
             grind)
          | (have r₁ := b2e15 (σ y) (σ x)
             have r₂ := b2e629
             grind)
          | exact resolve b2e15 b2e629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e629
        have b2e579303 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b2e579302
        have b2e579304 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e579303
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e579303
          | exact resolve b2e579303 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e579303
        have b2e580477 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e544
             have i₂ := b2e579304
             grind)
          | exact superpose b2e579304 b2e544
          | exact resolve b2e544 b2e579304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e544 b2e579304
        have b2e580530 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b2e580477
        have b2e581408 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e244 y x
             have i₂ := b2e580530
             grind)
          | exact superpose b2e580530 b2e244
          | (have j0 := b2e244 y x
             grind)
          | exact resolve b2e244 b2e580530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e244 b2e580530
        have b2e581751 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b2e581408
        have b2e581811 : x = (M.op x y) := by
          first
          | (have r₁ := b2e581751
             have r₂ := b2e621
             grind)
          | exact resolve b2e581751 b2e621
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e621 b2e581751
        have b2e582677 : x ≠ x ∨ y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e581811
             grind)
          | exact superpose b2e581811 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e581811
             grind)
          | exact resolve b2e16 b2e581811
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e582680 : y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by grind
        clear b2e582677
        have b2e584399 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e582680
             grind)
          | exact superpose b2e582680 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e582680
             grind)
          | exact resolve b2e15 b2e582680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e582680
        have b2e584428 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
        clear b2e584399
        have b2e584429 : x = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e584428
             have i₂ := b2e581811
             grind)
          | exact superpose b2e581811 b2e584428
          | exact resolve b2e584428 b2e581811
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e584428
        have b2e584430 : x = (k y x) := by grind
        clear b2e584429
        have b2e585279 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e378 x y
             have i₂ := b2e584430
             grind)
          | exact superpose b2e584430 b2e378
          | (have j0 := b2e378 x y
             grind)
          | exact resolve b2e378 b2e584430
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e378 b2e584430
        have b2e585489 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e585279
        have b2e586946 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e585489
             grind)
          | exact superpose b2e585489 b2e19
          | exact resolve b2e19 b2e585489
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e585489
        have b2e586963 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e586946
             have i₂ := b2e581811
             grind)
          | exact superpose b2e581811 b2e586946
          | exact resolve b2e586946 b2e581811
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e581811 b2e586946
        have b2e586964 : False := by grind
        exact b2e586964
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op (M.op x y) (M.op y y)) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e37 : y ≠ (M.op y (M.op x x)) ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 y x
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b3e40 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b3e39
        have b3e41 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e40
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e40
          | exact resolve b3e40 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e42 : (σ y) ≠ (M.op (σ (k x y)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e15
          | (have j0 := b3e15 (σ y) (σ x)
             grind)
          | exact resolve b3e15 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : (σ y) ≠ (M.op (σ (k x y)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
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
        have b3e44 : y ≠ y ∨ x = (M.op (M.op x y) (M.op y y)) ∨ y = (k x y) := by
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
        have b3e47 : x = (M.op (M.op x y) (M.op y y)) ∨ y = (k x y) := by grind
        clear b3e44
        have b3e48 : y = (k x y) := by
          first
          | (have r₁ := b3e47
             have r₂ := b3e20
             grind)
          | exact resolve b3e47 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b3e59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e60 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e60 (σ X1) (σ X0)
             grind)
          | exact superpose b3e60 b3e18
          | (have j1 := b3e60 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e78 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e23 X1 X0
             have i₂ := b3e60 (τ X1) X0
             grind)
          | exact superpose b3e60 b3e23
          | (have j1 := b3e60 (τ X1) X0
             grind)
          | exact resolve b3e23 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e60
        have b3e237 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e78 X0 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e78
          | exact resolve b3e78 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e262 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e237 X0 X1
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e237
          | (have j0 := b3e237 X0 X1
             grind)
          | exact resolve b3e237 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e237
        have b3e387 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e77 x y
             grind)
          | exact superpose b3e77 b3e19
          | (have j1 := b3e77 x y
             grind)
          | exact resolve b3e19 b3e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e398 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e77 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e446 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e43
          | exact resolve b3e43 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e387
             have i₂ := b3e262 y x
             grind)
          | exact superpose b3e262 b3e387
          | (have j1 := b3e262 (σ y) (σ x)
             grind)
          | (have r₁ := b3e387
             have r₂ := b3e262 y x
             grind)
          | exact resolve b3e387 b3e262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e387
        have b3e596 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b3e595
        have b3e601 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e596
             grind)
          | exact superpose b3e596 b3e19
          | exact resolve b3e19 b3e596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e604 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e596
             grind)
          | exact superpose b3e596 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | (have r₁ := b3e16 (σ y) (σ x)
             have r₂ := b3e596
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e596
             grind)
          | exact resolve b3e16 b3e596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e606 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
        clear b3e604
        have b3e610 : (σ y) = (M.op (σ (k x y)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e606
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e606
          | exact resolve b3e606 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e606
        have b3e611 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e610
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e610
          | exact resolve b3e610 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e610
        have b3e612 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e611
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e611
          | exact resolve b3e611 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e611
        have b3e102722 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e446
             have i₂ := b3e612
             grind)
          | exact superpose b3e612 b3e446
          | (have r₁ := b3e446
             have r₂ := b3e612
             grind)
          | exact resolve b3e446 b3e612
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e446 b3e612
        have b3e102731 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b3e102722
        have b3e103475 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e596
             have i₂ := b3e102731
             grind)
          | exact superpose b3e102731 b3e596
          | exact resolve b3e596 b3e102731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e596 b3e102731
        have b3e103571 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b3e103475
        have b3e104364 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e262 y x
             have i₂ := b3e103571
             grind)
          | exact superpose b3e103571 b3e262
          | (have j0 := b3e262 y x
             grind)
          | exact resolve b3e262 b3e103571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e262 b3e103571
        have b3e104527 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b3e104364
        have b3e104587 : x = (M.op x y) := by
          first
          | (have r₁ := b3e104527
             have r₂ := b3e601
             grind)
          | exact resolve b3e104527 b3e601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e601 b3e104527
        have b3e104922 : x ≠ x ∨ y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e104587
             grind)
          | exact superpose b3e104587 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e104587
             grind)
          | exact resolve b3e16 b3e104587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e104927 : y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by grind
        clear b3e104922
        have b3e104929 : y = (M.op y (M.op x x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e104927
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e104927
          | exact resolve b3e104927 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104927
        have b3e105983 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e37
             have i₂ := b3e104929
             grind)
          | exact superpose b3e104929 b3e37
          | (have r₁ := b3e37
             have r₂ := b3e104929
             grind)
          | exact resolve b3e37 b3e104929
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e104929
        have b3e105992 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
        clear b3e105983
        have b3e105993 : x = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e105992
             have i₂ := b3e104587
             grind)
          | exact superpose b3e104587 b3e105992
          | exact resolve b3e105992 b3e104587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105992
        have b3e105994 : x = (k y x) := by grind
        clear b3e105993
        have b3e106560 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e398 x y
             have i₂ := b3e105994
             grind)
          | exact superpose b3e105994 b3e398
          | (have j0 := b3e398 x y
             grind)
          | exact resolve b3e398 b3e105994
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e398 b3e105994
        have b3e106656 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b3e106560
        have b3e107742 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e106656
             grind)
          | exact superpose b3e106656 b3e19
          | exact resolve b3e19 b3e106656
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106656
        have b3e107763 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e107742
             have i₂ := b3e104587
             grind)
          | exact superpose b3e104587 b3e107742
          | exact resolve b3e107742 b3e104587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104587 b3e107742
        have b3e107764 : False := by grind
        exact b3e107764
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b4e31 : y ≠ (M.op y (M.op x x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y x
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e32
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e32
            | exact resolve b4e32 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b4e59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e60 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e60 (σ X1) (σ X0)
               grind)
            | exact superpose b4e60 b4e19
            | (have j1 := b4e60 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X1 X0
               have i₂ := b4e60 (τ X1) X0
               grind)
            | exact superpose b4e60 b4e25
            | (have j1 := b4e60 (τ X1) X0
               grind)
            | exact resolve b4e25 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e60
          have b4e206 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e79 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e79
            | exact resolve b4e79 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79
          have b4e229 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e206 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e206
            | (have j0 := b4e206 X0 X1
               grind)
            | exact resolve b4e206 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e206
          have b4e347 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e78 x y
               grind)
            | exact superpose b4e78 b4e20
            | (have j1 := b4e78 x y
               grind)
            | exact resolve b4e20 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e357 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e583 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e347
               have i₂ := b4e229 y x
               grind)
            | exact superpose b4e229 b4e347
            | (have j1 := b4e229 (σ y) (σ x)
               grind)
            | (have r₁ := b4e347
               have r₂ := b4e229 y x
               grind)
            | exact resolve b4e347 b4e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e347
          have b4e584 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e583
          have b4e588 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e584
               grind)
            | exact superpose b4e584 b4e20
            | exact resolve b4e20 b4e584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e591 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e584
               grind)
            | exact superpose b4e584 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e584
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e584
               grind)
            | exact resolve b4e17 b4e584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e593 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e591
          have b4e596 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e593
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e593
            | exact resolve b4e593 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e593
          have b4e598 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e596
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e596
            | exact resolve b4e596 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e596
          have b4e102334 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e33
               have i₂ := b4e598
               grind)
            | exact superpose b4e598 b4e33
            | (have r₁ := b4e33
               have r₂ := b4e598
               grind)
            | exact resolve b4e33 b4e598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e598
          have b4e102343 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
          clear b4e102334
          have b4e102869 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e584
               have i₂ := b4e102343
               grind)
            | exact superpose b4e102343 b4e584
            | exact resolve b4e584 b4e102343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e584 b4e102343
          have b4e102966 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
          clear b4e102869
          have b4e103540 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e229 y x
               have i₂ := b4e102966
               grind)
            | exact superpose b4e102966 b4e229
            | (have j0 := b4e229 y x
               grind)
            | exact resolve b4e229 b4e102966
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229 b4e102966
          have b4e103704 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b4e103540
          have b4e103764 : x = (M.op x y) := by
            first
            | (have r₁ := b4e103704
               have r₂ := b4e588
               grind)
            | exact resolve b4e103704 b4e588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e588 b4e103704
          have b4e104302 : x ≠ x ∨ y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e103764
               grind)
            | exact superpose b4e103764 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e103764
               grind)
            | exact resolve b4e17 b4e103764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e104307 : y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by grind
          clear b4e104302
          have b4e104309 : y = (M.op y (M.op x x)) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e104307
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e104307
            | exact resolve b4e104307 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104307
          have b4e105348 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e31
               have i₂ := b4e104309
               grind)
            | exact superpose b4e104309 b4e31
            | (have r₁ := b4e31
               have r₂ := b4e104309
               grind)
            | exact resolve b4e31 b4e104309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e104309
          have b4e105357 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
          clear b4e105348
          have b4e105358 : x = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e105357
               have i₂ := b4e103764
               grind)
            | exact superpose b4e103764 b4e105357
            | exact resolve b4e105357 b4e103764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105357
          have b4e105359 : x = (k y x) := by grind
          clear b4e105358
          have b4e105952 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e357 x y
               have i₂ := b4e105359
               grind)
            | exact superpose b4e105359 b4e357
            | (have j0 := b4e357 x y
               grind)
            | exact resolve b4e357 b4e105359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e357 b4e105359
          have b4e106050 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e105952
          have b4e107022 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e106050
               grind)
            | exact superpose b4e106050 b4e20
            | exact resolve b4e20 b4e106050
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e106050
          have b4e107041 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e107022
               have i₂ := b4e103764
               grind)
            | exact superpose b4e103764 b4e107022
            | exact resolve b4e107022 b4e103764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103764 b4e107022
          have b4e107042 : False := by grind
          exact b4e107042
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op (M.op x y) (M.op y y)) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e40 : y ≠ y ∨ x = (M.op (M.op x y) (M.op y y)) ∨ y = (k x y) := by
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
          have b5e41 : x = (M.op (M.op x y) (M.op y y)) ∨ y = (k x y) := by grind
          clear b5e40
          have b5e42 : y = (k x y) := by
            first
            | (have r₁ := b5e41
               have r₂ := b5e21
               grind)
            | exact resolve b5e41 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e48 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e52 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e48 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e53 (σ X1) (σ X0)
               grind)
            | exact superpose b5e53 b5e19
            | (have j1 := b5e53 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e385 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e486 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e385 y x
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e385
            | (have j0 := b5e385 y x
               grind)
            | exact resolve b5e385 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e385
          have b5e490 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e486
          have b5e493 : False := by grind
          exact b5e493
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e22 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by grind
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
        have b6e38 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b6e39 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
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
        have b6e41 : (σ y) ≠ (M.op (σ (k x y)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | exact resolve b6e15 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : (σ y) ≠ (M.op (σ (k x y)) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
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
        have b6e58 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e63 (σ X1) (σ X0)
             grind)
          | exact superpose b6e63 b6e18
          | (have j1 := b6e63 (σ X1) (σ X0)
             grind)
          | exact resolve b6e18 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e82 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e23 X1 X0
             have i₂ := b6e63 (τ X1) X0
             grind)
          | exact superpose b6e63 b6e23
          | (have j1 := b6e63 (τ X1) X0
             grind)
          | exact resolve b6e23 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e63
        have b6e225 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e82 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e82
          | exact resolve b6e82 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e225 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e225
          | (have j0 := b6e225 X0 X1
             grind)
          | exact resolve b6e225 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e225
        have b6e374 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e80 x y
             grind)
          | exact superpose b6e80 b6e19
          | (have j1 := b6e80 x y
             grind)
          | exact resolve b6e19 b6e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e385 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e80 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e578 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e374
             have i₂ := b6e250 y x
             grind)
          | exact superpose b6e250 b6e374
          | (have j1 := b6e250 (σ y) (σ x)
             grind)
          | (have r₁ := b6e374
             have r₂ := b6e250 y x
             grind)
          | exact resolve b6e374 b6e250
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e374
        have b6e579 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b6e578
        have b6e584 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e579
             grind)
          | exact superpose b6e579 b6e19
          | exact resolve b6e19 b6e579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e587 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e579
             grind)
          | exact superpose b6e579 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e579
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e579
             grind)
          | exact resolve b6e16 b6e579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e589 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
        clear b6e587
        have b6e593 : (σ y) = (M.op (σ (k x y)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e589
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e589
          | exact resolve b6e589 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e589
        have b6e594 : (σ y) = (M.op (σ (k x y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e593
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e593
          | exact resolve b6e593 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e593
        have b6e532422 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e594
             grind)
          | exact superpose b6e594 b6e42
          | (have r₁ := b6e42
             have r₂ := b6e594
             grind)
          | exact resolve b6e42 b6e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e594
        have b6e532426 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b6e532422
        have b6e533060 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e579
             have i₂ := b6e532426
             grind)
          | exact superpose b6e532426 b6e579
          | exact resolve b6e579 b6e532426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e579 b6e532426
        have b6e533111 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
        clear b6e533060
        have b6e533720 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e250 y x
             have i₂ := b6e533111
             grind)
          | exact superpose b6e533111 b6e250
          | (have j0 := b6e250 y x
             grind)
          | exact resolve b6e250 b6e533111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e250 b6e533111
        have b6e534000 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b6e533720
        have b6e534060 : x = (M.op x y) := by
          first
          | (have r₁ := b6e534000
             have r₂ := b6e584
             grind)
          | exact resolve b6e534000 b6e584
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e584 b6e534000
        have b6e534660 : x ≠ x ∨ y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e534060
             grind)
          | exact superpose b6e534060 b6e16
          | (have j0 := b6e16 y x
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e534060
             grind)
          | exact resolve b6e16 b6e534060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e534663 : y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by grind
        clear b6e534660
        have b6e536483 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e534663
             grind)
          | exact superpose b6e534663 b6e15
          | (have j0 := b6e15 y x
             grind)
          | (have r₁ := b6e15 y x
             have r₂ := b6e534663
             grind)
          | exact resolve b6e15 b6e534663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e534663
        have b6e536500 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
        clear b6e536483
        have b6e536516 : x = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e536500
             have i₂ := b6e534060
             grind)
          | exact superpose b6e534060 b6e536500
          | exact resolve b6e536500 b6e534060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e536500
        have b6e536517 : x = (k y x) := by grind
        clear b6e536516
        have b6e537172 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e385 x y
             have i₂ := b6e536517
             grind)
          | exact superpose b6e536517 b6e385
          | (have j0 := b6e385 x y
             grind)
          | exact resolve b6e385 b6e536517
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e385 b6e536517
        have b6e537368 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b6e537172
        have b6e538631 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e537368
             grind)
          | exact superpose b6e537368 b6e19
          | exact resolve b6e19 b6e537368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e537368
        have b6e538648 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b6e538631
             have i₂ := b6e534060
             grind)
          | exact superpose b6e534060 b6e538631
          | exact resolve b6e538631 b6e534060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e534060 b6e538631
        have b6e538649 : False := by grind
        exact b6e538649
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e41 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e43 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e23
               grind)
            | exact resolve b7e42 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
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
          have b7e56 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e60 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e71 : y = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e61 x y
               grind)
            | exact superpose b7e61 b7e48
            | (have j1 := b7e61 x y
               grind)
            | exact resolve b7e48 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e61
          have b7e73 : y = (M.op y x) := by grind
          clear b7e71
          have b7e76 : False := by grind
          exact b7e76
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e56 (σ X1) (σ X0)
               grind)
            | exact superpose b8e56 b8e19
            | (have j1 := b8e56 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e56 (τ X1) X0
               grind)
            | exact superpose b8e56 b8e25
            | (have j1 := b8e56 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e56
          have b8e213 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e76 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e76
            | exact resolve b8e76 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e238 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e213 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e213
            | (have j0 := b8e213 X0 X1
               grind)
            | exact resolve b8e213 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e213
          have b8e363 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e74 x y
               grind)
            | exact superpose b8e74 b8e20
            | (have j1 := b8e74 x y
               grind)
            | exact resolve b8e20 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e372 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e74 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e363
               have i₂ := b8e238 y x
               grind)
            | exact superpose b8e238 b8e363
            | (have j1 := b8e238 (σ y) (σ x)
               grind)
            | (have r₁ := b8e363
               have r₂ := b8e238 y x
               grind)
            | exact resolve b8e363 b8e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e363
          have b8e546 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e545
          have b8e550 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e546
               grind)
            | exact superpose b8e546 b8e20
            | exact resolve b8e20 b8e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e553 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e546
               grind)
            | exact superpose b8e546 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e546
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e546
               grind)
            | exact resolve b8e17 b8e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e555 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e553
          have b8e558 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e555
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e555
            | exact resolve b8e555 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e555
          have b8e563477 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e558
               grind)
            | exact superpose b8e558 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e558
               grind)
            | exact resolve b8e16 b8e558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e558
          have b8e563478 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
          clear b8e563477
          have b8e563479 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e563478
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e563478
            | exact resolve b8e563478 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e563478
          have b8e564054 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e546
               have i₂ := b8e563479
               grind)
            | exact superpose b8e563479 b8e546
            | exact resolve b8e546 b8e563479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e546 b8e563479
          have b8e564107 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
          clear b8e564054
          have b8e564716 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e238 y x
               have i₂ := b8e564107
               grind)
            | exact superpose b8e564107 b8e238
            | (have j0 := b8e238 y x
               grind)
            | exact resolve b8e238 b8e564107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238 b8e564107
          have b8e565057 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b8e564716
          have b8e565117 : x = (M.op x y) := by
            first
            | (have r₁ := b8e565057
               have r₂ := b8e550
               grind)
            | exact resolve b8e565057 b8e550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e550 b8e565057
          have b8e565824 : x ≠ x ∨ y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e565117
               grind)
            | exact superpose b8e565117 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e565117
               grind)
            | exact resolve b8e17 b8e565117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e565827 : y = (M.op (M.op y x) (M.op x x)) ∨ x = (k y x) := by grind
          clear b8e565824
          have b8e567640 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e565827
               grind)
            | exact superpose b8e565827 b8e16
            | (have j0 := b8e16 y x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e565827
               grind)
            | exact resolve b8e16 b8e565827
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e565827
          have b8e567669 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
          clear b8e567640
          have b8e567697 : x = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e567669
               have i₂ := b8e565117
               grind)
            | exact superpose b8e565117 b8e567669
            | exact resolve b8e567669 b8e565117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e567669
          have b8e567698 : x = (k y x) := by grind
          clear b8e567697
          have b8e568302 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e372 x y
               have i₂ := b8e567698
               grind)
            | exact superpose b8e567698 b8e372
            | (have j0 := b8e372 x y
               grind)
            | exact resolve b8e372 b8e567698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e372 b8e567698
          have b8e568511 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e568302
          have b8e569929 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e568511
               grind)
            | exact superpose b8e568511 b8e20
            | exact resolve b8e20 b8e568511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e568511
          have b8e569946 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e569929
               have i₂ := b8e565117
               grind)
            | exact superpose b8e565117 b8e569929
            | exact resolve b8e569929 b8e565117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e565117 b8e569929
          have b8e569947 : False := by grind
          exact b8e569947

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),X) = m(m(Y,Y),Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxyx_ppyyy_pxy_x_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) a ≠ M.op (M.op b b) b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (M.op (M.op b b) b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) a = M.op (M.op b b) b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (M.op (M.op b b) b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) a = M.op (M.op b b) b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (M.op (M.op b b) b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) x) (M.op (M.op y y) y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x y) x) = (M.op (M.op y y) y) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e45 : (M.op (M.op y y) y) ≠ (M.op (M.op y y) y) ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 y y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ y) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e46
      have b0e49 : (M.op x y) = (k x y) := by grind
      clear b0e45
      have b0e50 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e48
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e48
        | exact resolve b0e48 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e51 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e50
           have i₂ := b0e49
           grind)
        | exact superpose b0e49 b0e50
        | exact resolve b0e50 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49 b0e50
      have b0e52 : False := by grind
      exact b0e52
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op (M.op x y) x) = (M.op (M.op y y) y) := by grind
        have b1e21 : (M.op (M.op (σ x) (σ y)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : (M.op (M.op y y) y) ≠ (M.op (M.op y y) y) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : (M.op x y) = (k x y) := by grind
        clear b1e41
        have b1e54 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e56 : (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e54
        have b1e57 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e56
             have r₂ := b1e23
             grind)
          | exact resolve b1e56 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e56
        have b1e58 : (σ x) = (σ (k x y)) := by
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
        have b1e59 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e58
          | exact resolve b1e58 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e58
        have b1e60 : False := by grind
        exact b1e60
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op x y) x) = (M.op (M.op y y) y) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : (M.op (M.op y y) y) ≠ (M.op (M.op y y) y) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 y y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : (M.op x y) = (k x y) := by grind
        clear b2e38
        have b2e57 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e15 (M.op X1 X1) X1
             have r₂ := b2e17 (M.op (M.op X1 X1) X1) (M.op X1 X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e66 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e66 (σ X1) (σ X0)
             grind)
          | exact superpose b2e66 b2e18
          | (have j1 := b2e66 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e530 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e84 x y
             grind)
          | exact superpose b2e84 b2e19
          | (have j1 := b2e84 x y
             grind)
          | exact resolve b2e19 b2e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e551 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e530
             have r₂ := b2e22
             grind)
          | exact resolve b2e530 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e530
        have b2e557 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e551
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e551
          | exact resolve b2e551 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e551
        have b2e558 : False := by grind
        exact b2e558
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op (M.op x y) x) ≠ (M.op (M.op y y) y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op (M.op y y) y) ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ y) (σ y)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e41
        have b3e44 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b3e55 : x ≠ x ∨ (M.op (M.op y y) y) = (M.op x x) ∨ x = (k x y) := by
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
        have b3e57 : (M.op (M.op y y) y) = (M.op x x) ∨ x = (k x y) := by grind
        clear b3e55
        have b3e59 : x = (k x y) := by
          first
          | (have r₁ := b3e57
             have r₂ := b3e23
             grind)
          | exact resolve b3e57 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e57
        have b3e96 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e44
             grind)
          | exact superpose b3e44 b3e24
          | exact resolve b3e24 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e44
        have b3e102 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e96
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e96
          | exact resolve b3e96 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e96
        have b3e103 : False := by grind
        exact b3e103
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
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op (M.op x y) x) ≠ (M.op (M.op y y) y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op (M.op y y) y) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : x ≠ x ∨ (M.op (M.op y y) y) = (M.op x x) ∨ x = (k x y) := by
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
          have b5e54 : (M.op (M.op y y) y) = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e53
          have b5e55 : x = (k x y) := by
            first
            | (have r₁ := b5e54
               have r₂ := b5e25
               grind)
            | exact resolve b5e54 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e54
          have b5e60 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e16 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e16 (M.op X1 X1) X1
               have r₂ := b5e18 (M.op (M.op X1 X1) X1) (M.op X1 X1)
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e70 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e69 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e70 (σ X1) (σ X0)
               grind)
            | exact superpose b5e70 b5e19
            | (have j1 := b5e70 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e549 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e735 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e549 x y
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e549
            | (have j0 := b5e549 x y
               grind)
            | exact resolve b5e549 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e549
          have b5e739 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e735
          have b5e742 : False := by grind
          exact b5e742
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ y) (σ y)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e38
        have b6e41 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e40
          | exact resolve b6e40 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e61 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e19
          | exact resolve b6e19 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e73 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e15 X1 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e15 (M.op X1 X1) X1
             have r₂ := b6e17 (M.op (M.op X1 X1) X1) (M.op X1 X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e81 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e82 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e81 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e94 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e61
             have i₂ := b6e82 y x
             grind)
          | exact superpose b6e82 b6e61
          | (have j1 := b6e82 y x
             grind)
          | exact resolve b6e61 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e82
        have b6e95 : x = (M.op x y) := by grind
        clear b6e94
        have b6e96 : False := by grind
        exact b6e96
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (M.op (M.op (σ x) (σ y)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e66 : (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e65
          have b7e67 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e25
               grind)
            | exact resolve b7e66 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e66
          have b7e68 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e67
            | exact resolve b7e67 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e72 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e14
            | exact resolve b7e14 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e73 : x = (k x y) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e72
            | exact resolve b7e72 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e81 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X1 X0
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e16 X1 X1
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X0 X0
               have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | (have r₁ := b7e16 (M.op X1 X1) X1
               have r₂ := b7e18 (M.op (M.op X1 X1) X1) (M.op X1 X1)
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e90 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e91 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e90 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e100 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e91 y x
               grind)
            | exact superpose b7e91 b7e73
            | (have j1 := b7e91 y x
               grind)
            | exact resolve b7e73 b7e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e91
          have b7e102 : x = (M.op x y) := by grind
          clear b7e100
          have b7e105 : False := by grind
          exact b7e105
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X1) X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e83 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 (M.op X1 X1) X1
               have r₂ := b8e18 (M.op (M.op X1 X1) X1) (M.op X1 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e92 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e91 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e92 (σ X1) (σ X0)
               grind)
            | exact superpose b8e92 b8e19
            | (have j1 := b8e92 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e109 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e92 (τ X1) X0
               grind)
            | exact superpose b8e92 b8e26
            | (have j1 := b8e92 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e92
          have b8e382 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e109 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e109
            | exact resolve b8e109 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e416 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e382 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e382
            | (have j0 := b8e382 X0 X1
               grind)
            | exact resolve b8e382 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e382
          have b8e566 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e105 x y
               grind)
            | exact superpose b8e105 b8e20
            | (have j1 := b8e105 x y
               grind)
            | exact resolve b8e20 b8e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e587 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e566
               have r₂ := b8e24
               grind)
            | exact resolve b8e566 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e566
          have b8e597 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e587
               have i₂ := b8e416 y x
               grind)
            | exact superpose b8e416 b8e587
            | (have j1 := b8e416 y x
               grind)
            | (have r₁ := b8e587
               have r₂ := b8e416 y x
               grind)
            | exact resolve b8e587 b8e416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e416 b8e587
          have b8e598 : x = (M.op x y) := by grind
          clear b8e597
          have b8e600 : False := by grind
          exact b8e600

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),X) = m(X,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxyx_pxy_pxy_x_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op (M.op x y) x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op (M.op x y) x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b1e30 : (M.op x y) = (k x y) := by grind
        clear b1e29
        have b1e31 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e34 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e31
        have b1e36 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e34
             have r₂ := b1e23
             grind)
          | exact resolve b1e34 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e34
        have b1e37 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e36
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e36
          | exact resolve b1e36 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e38 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e37
          | exact resolve b1e37 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e37
        have b1e39 : False := by grind
        exact b1e39
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op (M.op x y) x) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b2e44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 (M.op X1 X1) X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e44 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e48 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e49 (σ X0) (σ X1)
             grind)
          | exact superpose b2e49 b2e18
          | (have j1 := b2e49 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e355 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e64 x y
             grind)
          | exact superpose b2e64 b2e19
          | (have j1 := b2e64 x y
             grind)
          | exact resolve b2e19 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e363 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e355
             have r₂ := b2e22
             grind)
          | exact resolve b2e355 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e355
        have b2e367 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e363
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e363
          | exact resolve b2e363 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e363
        have b2e368 : False := by grind
        exact b2e368
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x y) ≠ (M.op (M.op x y) x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have i₁ := b3e15 (M.op (σ x) (σ y)) (σ x)
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
        have b3e41 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e42 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e41
        have b3e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e42
          | exact resolve b3e42 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e47 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by
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
        have b3e48 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have i₁ := b3e16 (M.op (σ x) (σ y)) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (M.op (σ x) (σ y)) (σ x)
             grind)
          | (have r₁ := b3e16 (M.op (σ x) (σ y)) (σ x)
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
        clear b3e48
        have b3e51 : x = (M.op x x) ∨ x = (k x y) := by grind
        clear b3e47
        have b3e52 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e40
             grind)
          | exact resolve b3e50 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e50
        have b3e53 : x = (k x y) := by
          first
          | (have r₁ := b3e51
             have r₂ := b3e23
             grind)
          | exact resolve b3e51 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e54 : (σ (k x y)) = (k (σ (k x y)) (σ x)) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e52
          | exact resolve b3e52 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e52
        have b3e55 : (σ (k x y)) = (σ (k (k x y) x)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e18 (k x y) x
             grind)
          | exact superpose b3e18 b3e54
          | exact resolve b3e54 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e56 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e55
          | exact resolve b3e55 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e55
        have b3e58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 (M.op X1 X1) X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e67 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e13
          | exact resolve b3e13 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e68 : x = (k x x) := by
          first
          | (have i₁ := b3e67
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e67
          | exact resolve b3e67 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e82 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e63 x x
             have i₂ := b3e68
             grind)
          | exact superpose b3e68 b3e63
          | (have j0 := b3e63 x x
             grind)
          | exact resolve b3e63 b3e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63 b3e68
        have b3e83 : x = (M.op x x) := by grind
        clear b3e82
        have b3e85 : False := by grind
        exact b3e85
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
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op (M.op x y) x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by
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
          have b5e51 : x = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e50
          have b5e52 : x = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e25
               grind)
            | exact resolve b5e51 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e51
          have b5e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 (M.op X1 X1) X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e59 (σ X0) (σ X1)
               grind)
            | exact superpose b5e59 b5e19
            | (have j1 := b5e59 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e362 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e464 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e362 x y
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e362
            | (have j0 := b5e362 x y
               grind)
            | exact resolve b5e362 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e362
          have b5e468 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e464
          have b5e471 : False := by grind
          exact b5e471
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 (M.op X1 X1) X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e86 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e57 x y
             grind)
          | exact superpose b6e57 b6e42
          | (have j1 := b6e57 x y
             grind)
          | exact resolve b6e42 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e57
        have b6e87 : x = (M.op x y) := by grind
        clear b6e86
        have b6e90 : False := by grind
        exact b6e90
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e43 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e44 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e25
               grind)
            | exact resolve b7e43 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e43
          have b7e45 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e44
            | exact resolve b7e44 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : (k x y) = (τ (σ x)) := by
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
          have b7e49 : x = (k x y) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e48
            | exact resolve b7e48 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 (M.op X1 X1) X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e66 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e58 x y
               grind)
            | exact superpose b7e58 b7e49
            | (have j1 := b7e58 x y
               grind)
            | exact resolve b7e49 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49 b7e58
          have b7e68 : x = (M.op x y) := by grind
          clear b7e66
          have b7e71 : False := by grind
          exact b7e71
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 (M.op X1 X1) X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e54 (σ X0) (σ X1)
               grind)
            | exact superpose b8e54 b8e19
            | (have j1 := b8e54 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e54 X0 (τ X1)
               grind)
            | exact superpose b8e54 b8e26
            | (have j1 := b8e54 X0 (τ X1)
               grind)
            | exact resolve b8e26 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e54
          have b8e200 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e74 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e74
            | exact resolve b8e74 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e225 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e200 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e200
            | (have j0 := b8e200 X0 X1
               grind)
            | exact resolve b8e200 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e200
          have b8e348 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e71 x y
               grind)
            | exact superpose b8e71 b8e20
            | (have j1 := b8e71 x y
               grind)
            | exact resolve b8e20 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e356 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e348
               have r₂ := b8e24
               grind)
            | exact resolve b8e348 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e348
          have b8e361 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e356
               have i₂ := b8e225 y x
               grind)
            | exact superpose b8e225 b8e356
            | (have j1 := b8e225 y x
               grind)
            | (have r₁ := b8e356
               have r₂ := b8e225 y x
               grind)
            | exact resolve b8e356 b8e225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e225 b8e356
          have b8e362 : x = (M.op x y) := by grind
          clear b8e361
          have b8e364 : False := by grind
          exact b8e364

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxyx_y_pxy_pyx_pxy_pyx_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op (M.op x y) x) := by grind
      have b0e20 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
      have b0e30 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X0 X1) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op (M.op x y) x) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e39 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
        have b1e40 : (M.op x y) = (k x y) := by grind
        clear b1e39
        have b1e45 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e45
        have b1e50 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j1 := b1e15 (σ x) (σ y)
             grind)
          | (have r₁ := b1e47
             have r₂ := b1e15 (σ x) (σ y)
             grind)
          | exact resolve b1e47 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e52 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b1e54 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e52
          | exact resolve b1e52 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e52
        have b1e55 : False := by grind
        exact b1e55
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op (M.op x y) x) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
        have b2e57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e62 (σ X1) (σ X0)
             grind)
          | exact superpose b2e62 b2e18
          | (have j1 := b2e62 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e505 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e96 x y
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e96 y x
             grind)
          | exact superpose b2e96 b2e22
          | (have j1 := b2e96 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e96 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e96 y x
             grind)
          | exact resolve b2e22 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96
        have b2e512 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
        clear b2e505
        have b2e519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e512
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e512
          | exact resolve b2e512 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e512
        have b2e530 : False := by grind
        exact b2e530
  · rcases eq_or_ne (M.op x y) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X0 X1) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : (M.op x y) = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e39 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e39
        have b3e41 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e40
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e40
          | exact resolve b3e40 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e43 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e19
          | exact resolve b3e19 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e47 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) := by
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
          | (have r₁ := b3e16 y x
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) := by grind
        clear b3e47
        have b3e54 : (M.op x y) = (k x y) := by
          first
          | (have j1 := b3e15 x y
             grind)
          | (have r₁ := b3e50
             have r₂ := b3e15 x y
             grind)
          | exact resolve b3e50 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e96 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e43
          | exact resolve b3e43 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e54
        have b3e97 : False := by grind
        exact b3e97
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X0 X1) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e64 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) := by
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
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b4e65
          have b4e68 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) := by grind
          clear b4e64
          have b4e72 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b4e16 (σ x) (σ y)
               grind)
            | (have r₁ := b4e67
               have r₂ := b4e16 (σ x) (σ y)
               grind)
            | exact resolve b4e67 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e73 : (M.op x y) = (k x y) := by
            first
            | (have j1 := b4e16 x y
               grind)
            | (have r₁ := b4e68
               have r₂ := b4e16 x y
               grind)
            | exact resolve b4e68 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e76 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e72
            | exact resolve b4e72 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e78 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e76
               have i₂ := b4e73
               grind)
            | exact superpose b4e73 b4e76
            | exact resolve b4e76 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73 b4e76
          have b4e80 : False := by grind
          exact b4e80
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X0 X1) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : (M.op x y) = (M.op y x) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e61 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) := by
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
            | (have r₁ := b5e17 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (k x y) := by grind
          clear b5e61
          have b5e66 : (M.op x y) = (k x y) := by
            first
            | (have j1 := b5e16 x y
               grind)
            | (have r₁ := b5e63
               have r₂ := b5e16 x y
               grind)
            | exact resolve b5e63 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e89 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e93 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e89 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89
          have b5e94 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e93 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e126 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e94 (σ X1) (σ X0)
               grind)
            | exact superpose b5e94 b5e19
            | (have j1 := b5e94 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94
          have b5e455 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e126 x y
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e126 y x
               grind)
            | exact superpose b5e126 b5e24
            | (have j1 := b5e126 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e126 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e126 y x
               grind)
            | exact resolve b5e24 b5e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e126
          have b5e462 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b5e455
          have b5e469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e462
               have i₂ := b5e66
               grind)
            | exact superpose b5e66 b5e462
            | exact resolve b5e462 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e462
          have b5e481 : False := by grind
          exact b5e481
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ x)) ((σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e70 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e74 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e70 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e75 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e74 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e85 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e75 y x
             grind)
          | exact superpose b6e75 b6e42
          | (have j1 := b6e75 x y
             grind)
          | exact resolve b6e42 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e75
        have b6e86 : (M.op x y) = (M.op y x) := by grind
        clear b6e85
        have b6e87 : False := by grind
        exact b6e87
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X0 X1) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : (M.op x y) ≠ (M.op y x) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e47 : (σ x) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e47
            | exact resolve b7e47 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e61 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e17 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ y) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e62 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e62
          have b7e65 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b7e61
          have b7e67 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b7e16 (σ x) (σ y)
               grind)
            | (have r₁ := b7e64
               have r₂ := b7e16 (σ x) (σ y)
               grind)
            | exact resolve b7e64 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e68 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e69 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e67
            | exact resolve b7e67 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e70 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e48
               grind)
            | exact resolve b7e68 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e68
          have b7e71 : (σ (k y x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e70
            | exact resolve b7e70 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69 b7e70
          have b7e93 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X1 X0
               have i₂ := b7e18 X1 X0
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X0
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e97 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e93 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e98 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e97 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e105 : (k y x) = (τ (σ (k x y))) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e14
            | exact resolve b7e14 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e106 : (k y x) = (k x y) := by
            first
            | (have i₁ := b7e105
               have i₂ := b7e14 (k x y)
               grind)
            | exact superpose b7e14 b7e105
            | exact resolve b7e105 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e122 : (M.op y x) = (k x y) ∨ (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b7e106
               have i₂ := b7e98 x y
               grind)
            | exact superpose b7e98 b7e106
            | (have j1 := b7e98 x y
               grind)
            | exact resolve b7e106 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106
          have b7e125 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b7e122
               have r₂ := b7e22
               grind)
            | exact resolve b7e122 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122
          have b7e128 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b7e98 y x
               have i₂ := b7e125
               grind)
            | exact superpose b7e125 b7e98
            | (have j0 := b7e98 x y
               grind)
            | exact resolve b7e98 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e125
          have b7e129 : (M.op x y) = (M.op y x) := by grind
          clear b7e128
          have b7e131 : False := by grind
          exact b7e131
        · have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y x) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e82 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e86 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e82 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e87 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e86 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e102 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e87 (σ X1) (σ X0)
               grind)
            | exact superpose b8e87 b8e19
            | (have j1 := b8e87 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e497 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e102 x y
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e102 y x
               grind)
            | exact superpose b8e102 b8e24
            | (have j1 := b8e102 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e102 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e102 y x
               grind)
            | exact resolve b8e24 b8e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e504 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b8e497
          have b8e527 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e504
               grind)
            | exact superpose b8e504 b8e20
            | exact resolve b8e20 b8e504
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e504
          have b8e550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b8e527
               have i₂ := b8e87 y x
               grind)
            | exact superpose b8e87 b8e527
            | (have j1 := b8e87 x y
               grind)
            | exact resolve b8e527 b8e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87 b8e527
          have b8e551 : (M.op x y) = (M.op y x) := by grind
          clear b8e550
          have b8e552 : False := by grind
          exact b8e552
