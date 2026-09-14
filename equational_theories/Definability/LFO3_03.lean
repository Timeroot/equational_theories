import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),Y) = m(m(Y,Y),Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxyy_ppyyy_x_y_pyx_x_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 1)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 1)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) b ≠ M.op (M.op b b) b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op (M.op b b) b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) b = M.op (M.op b b) b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op (M.op b b) b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) b = M.op (M.op b b) b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op (M.op b b) b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) y) (M.op (M.op y y) y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 X1) X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e48 (σ X0)
           grind)
        | exact superpose b0e48 b0e17
        | exact resolve b0e17 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e54 X0
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e54
        | exact resolve b0e54 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e54
      have b0e72 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e16 (M.op X0 X1) (k X1 X0)
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op (M.op X0 X1) X1) (M.op (M.op X1 X1) X1)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e78 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e72 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72
      have b0e79 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e78 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e82 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e79 (τ X0) X1
           grind)
        | exact superpose b0e79 b0e23
        | (have j1 := b0e79 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e79 (σ X0) (σ X1)
           grind)
        | exact superpose b0e79 b0e17
        | (have j1 := b0e79 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e197 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e82 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e82
        | exact resolve b0e82 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82
      have b0e213 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e197 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e197
        | (have j0 := b0e197 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e197 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e197
      have b0e523 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e83 x y
           grind)
        | exact superpose b0e83 b0e18
        | (have j1 := b0e83 x y
           grind)
        | exact resolve b0e18 b0e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e547 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e523
           have i₂ := b0e213 x y
           grind)
        | exact superpose b0e213 b0e523
        | (have j1 := b0e213 (σ x) (σ y)
           grind)
        | (have r₁ := b0e523
           have r₂ := b0e213 x y
           grind)
        | (have r₁ := b0e523
           have r₂ := b0e213 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e523
           have r₂ := b0e213 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e523 b0e213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e213 b0e523
      have b0e548 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e547
      have b0e601 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e12 x
           have i₂ := b0e548
           grind)
        | exact superpose b0e548 b0e12
        | exact resolve b0e12 b0e548
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e548
      have b0e634 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e601
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e601
        | exact resolve b0e601 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e601
      have b0e635 : x = y := by grind
      clear b0e634
      have b0e692 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e635
           grind)
        | exact superpose b0e635 b0e18
        | exact resolve b0e18 b0e635
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e635
      have b0e695 : False := by grind
      exact b0e695
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : False := by grind
        exact b1e25
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 X1) X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e56 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
             have j1 := b2e17 (M.op X0 X1) (k X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op (M.op X0 X1) X1) (M.op (M.op X1 X1) X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e65 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e25 X0 X1
             have i₂ := b2e65 (τ X0) X1
             grind)
          | exact superpose b2e65 b2e25
          | (have j1 := b2e65 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b2e25 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e65 (σ X0) (σ X1)
             grind)
          | exact superpose b2e65 b2e18
          | (have j1 := b2e65 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e160 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e70 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e70
          | exact resolve b2e70 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e160 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e160
          | (have j0 := b2e160 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b2e160 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e160
        have b2e515 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e71 x y
             grind)
          | exact superpose b2e71 b2e19
          | (have j1 := b2e71 x y
             grind)
          | exact resolve b2e19 b2e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e532 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e515
             have r₂ := b2e22
             grind)
          | exact resolve b2e515 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e515
        have b2e543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b2e532
             have i₂ := b2e176 x y
             grind)
          | exact superpose b2e176 b2e532
          | (have j1 := b2e176 x y
             grind)
          | (have r₁ := b2e532
             have r₂ := b2e176 x y
             grind)
          | (have r₁ := b2e532
             have r₂ := b2e176 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b2e532
             have r₂ := b2e176 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b2e532 b2e176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e176 b2e532
        have b2e544 : x = y := by grind
        clear b2e543
        have b2e597 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e544
             grind)
          | exact superpose b2e544 b2e22
          | exact resolve b2e22 b2e544
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e544
        have b2e601 : False := by grind
        exact b2e601
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
      · have b3e20 : (M.op (M.op x y) y) ≠ (M.op (M.op y y) y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 X1) X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e57 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
             have j1 := b6e17 (M.op X0 X1) (k X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op (M.op X0 X1) X1) (M.op (M.op X1 X1) X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e66 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e69 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e25 X0 X1
             have i₂ := b6e66 (τ X0) X1
             grind)
          | exact superpose b6e66 b6e25
          | (have j1 := b6e66 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b6e25 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e66 (σ X0) (σ X1)
             grind)
          | exact superpose b6e66 b6e18
          | (have j1 := b6e66 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b6e18 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e160 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e69 (σ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e69
          | exact resolve b6e69 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e160 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e160
          | (have j0 := b6e160 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b6e160 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e160
        have b6e512 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e70 x y
             grind)
          | exact superpose b6e70 b6e19
          | (have j1 := b6e70 x y
             grind)
          | exact resolve b6e19 b6e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e512
             have i₂ := b6e176 x y
             grind)
          | exact superpose b6e176 b6e512
          | (have j1 := b6e176 (σ x) (σ y)
             grind)
          | (have r₁ := b6e512
             have r₂ := b6e176 x y
             grind)
          | (have r₁ := b6e512
             have r₂ := b6e176 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b6e512
             have r₂ := b6e176 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b6e512 b6e176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e176 b6e512
        have b6e536 : (σ x) = (σ y) ∨ x = y := by grind
        clear b6e535
        have b6e538 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e536
             have r₂ := b6e21
             grind)
          | exact resolve b6e536 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e536
        have b6e591 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e538
             grind)
          | exact superpose b6e538 b6e13
          | exact resolve b6e13 b6e538
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e538
        have b6e624 : x = y := by
          first
          | (have i₁ := b6e591
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e591
          | exact resolve b6e591 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e591
        have b6e627 : False := by grind
        exact b6e627
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : False := by grind
          exact b7e27
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 X1) X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e66 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
               have j1 := b8e18 (M.op X0 X1) (k X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X1) X1) (M.op (M.op X1 X1) X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e66 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e77 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e84 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e77 (τ X0) X1
               grind)
            | exact superpose b8e77 b8e27
            | (have j1 := b8e77 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e27 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e77 (σ X0) (σ X1)
               grind)
            | exact superpose b8e77 b8e19
            | (have j1 := b8e77 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e151 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e84 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e84
            | exact resolve b8e84 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e167 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e151 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e151
            | (have j0 := b8e151 (σ (k X1 X0)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e151 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151
          have b8e506 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e85 x y
               grind)
            | exact superpose b8e85 b8e20
            | (have j1 := b8e85 x y
               grind)
            | exact resolve b8e20 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e523 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e506
               have r₂ := b8e24
               grind)
            | exact resolve b8e506 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e506
          have b8e534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e523
               have i₂ := b8e167 x y
               grind)
            | exact superpose b8e167 b8e523
            | (have j1 := b8e167 x y
               grind)
            | (have r₁ := b8e523
               have r₂ := b8e167 x y
               grind)
            | (have r₁ := b8e523
               have r₂ := b8e167 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e523
               have r₂ := b8e167 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e523 b8e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167 b8e523
          have b8e535 : x = y := by grind
          clear b8e534
          have b8e537 : False := by grind
          exact b8e537

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),Y) = m(X,Y) then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxyy_pxy_pxy_x_pxy_pyx_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) b ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) b = M.op a b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) b = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) y) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op (M.op x y) y) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
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
      have b0e36 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
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
      have b0e37 : False := by grind
      exact b0e37
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : False := by grind
        exact b1e25
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op (M.op x y) y) := by grind
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
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X0 X1) X1
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
        have b2e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e354 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e63 x y
             grind)
          | exact superpose b2e63 b2e19
          | (have j1 := b2e63 x y
             grind)
          | exact resolve b2e19 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e361 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e354
             have r₂ := b2e22
             grind)
          | exact resolve b2e354 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e354
        have b2e365 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e361
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e361
          | exact resolve b2e361 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e361
        have b2e366 : False := by grind
        exact b2e366
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x y) ≠ (M.op (M.op x y) y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ (M.op x y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : False := by grind
        exact b3e25
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : False := by grind
          exact b4e28
        · have b5e21 : (M.op x y) ≠ (M.op (M.op x y) y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ (M.op x y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27 : False := by grind
          exact b5e27
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
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
        have b6e45 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X0 X1) X1
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
        have b6e85 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e45
             have i₂ := b6e57 x y
             grind)
          | exact superpose b6e57 b6e45
          | (have j1 := b6e57 x y
             grind)
          | exact resolve b6e45 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45 b6e57
        have b6e86 : x = (M.op x y) := by grind
        clear b6e85
        have b6e89 : False := by grind
        exact b6e89
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : False := by grind
          exact b7e27
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X1) X1
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
          have b8e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e73 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
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
          have b8e171 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e73 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e73
            | exact resolve b8e73 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e171 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e171
            | (have j0 := b8e171 X0 X1
               grind)
            | exact resolve b8e171 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171
          have b8e309 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e316 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e309
               have r₂ := b8e24
               grind)
            | exact resolve b8e309 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309
          have b8e321 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e316
               have i₂ := b8e194 y x
               grind)
            | exact superpose b8e194 b8e316
            | (have j1 := b8e194 y x
               grind)
            | (have r₁ := b8e316
               have r₂ := b8e194 y x
               grind)
            | exact resolve b8e316 b8e194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e194 b8e316
          have b8e322 : x = (M.op x y) := by grind
          clear b8e321
          have b8e324 : False := by grind
          exact b8e324

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),Y) = m(Y,m(Y,X)) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxyy_pypyx_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) b ≠ M.op b (M.op b a) ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op b (M.op b a))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) b = M.op b (M.op b a) ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op b (M.op b a))).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) b = M.op b (M.op b a) ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op b (M.op b a))).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) y) (M.op y (M.op y x)) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x y) y) = (M.op y (M.op y x)) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e45 : (M.op y (M.op y x)) ≠ (M.op y (M.op y x)) ∨ (M.op x y) = (k x y) := by
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
      have b0e46 : (M.op (σ y) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op (M.op x y) y) = (M.op y (M.op y x)) := by grind
        have b1e21 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ y) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (σ y)) := by
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
        have b1e41 : (M.op y (M.op y x)) ≠ (M.op y (M.op y x)) ∨ (M.op x y) = (k x y) := by
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
        have b1e43 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (M.op (σ y) (σ x))) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e45 : (M.op (σ y) (M.op (σ y) (σ x))) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
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
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op x y) y) = (M.op y (M.op y x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : (M.op y (M.op y x)) ≠ (M.op y (M.op y x)) ∨ (M.op x y) = (k x y) := by
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
        have b2e52 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e56 (σ X1) (σ X0)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e357 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
        clear b2e74
        have b2e365 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e357
             have r₂ := b2e22
             grind)
          | exact resolve b2e357 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e357
        have b2e369 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e365
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e365
          | exact resolve b2e365 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e365
        have b2e370 : False := by grind
        exact b2e370
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op (M.op x y) y) ≠ (M.op y (M.op y x)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op y (M.op y x)) ≠ (M.op y y) := by
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
        have b3e41 : (M.op (σ y) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e47 : y ≠ y ∨ (M.op y (M.op y x)) = (M.op y y) ∨ y = (k x y) := by
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
        have b3e50 : (M.op y (M.op y x)) = (M.op y y) ∨ y = (k x y) := by grind
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
        have b3e77 : (σ y) ≠ (σ y) := by
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
        have b3e78 : False := by grind
        exact b3e78
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
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op (M.op x y) y) ≠ (M.op y (M.op y x)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y (M.op y x)) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : y ≠ y ∨ (M.op y (M.op y x)) = (M.op y y) ∨ y = (k x y) := by
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
          have b5e51 : (M.op y (M.op y x)) = (M.op y y) ∨ y = (k x y) := by grind
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
          have b5e55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e59 (σ X1) (σ X0)
               grind)
            | exact superpose b5e59 b5e19
            | (have j1 := b5e59 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e329 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e468 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e329 x y
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e329
            | (have j0 := b5e329 x y
               grind)
            | exact resolve b5e329 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e329
          have b5e472 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e468
          have b5e475 : False := by grind
          exact b5e475
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (M.op (σ y) (σ x))) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (σ y) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e54 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e78 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
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
        have b6e79 : y = (M.op x y) := by grind
        clear b6e78
        have b6e80 : False := by grind
        exact b6e80
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e62 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (M.op (σ y) (σ x))) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e63 : (M.op (σ y) (M.op (σ y) (σ x))) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
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
          have b7e78 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e81 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e82 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e91 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e82 y x
               grind)
            | exact superpose b7e82 b7e71
            | (have j1 := b7e82 y x
               grind)
            | exact resolve b7e71 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e82
          have b7e93 : y = (M.op x y) := by grind
          clear b7e91
          have b7e96 : False := by grind
          exact b7e96
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e72 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e76 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e75 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e76 (σ X1) (σ X0)
               grind)
            | exact superpose b8e76 b8e19
            | (have j1 := b8e76 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e83 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e76 X1 (τ X0)
               grind)
            | exact superpose b8e76 b8e25
            | (have j1 := b8e76 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e76
          have b8e173 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e83 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e83
            | exact resolve b8e83 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
          have b8e312 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e81 x y
               grind)
            | exact superpose b8e81 b8e20
            | (have j1 := b8e81 x y
               grind)
            | exact resolve b8e20 b8e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e320 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e312
               have r₂ := b8e24
               grind)
            | exact resolve b8e312 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e312
          have b8e325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e320
               have i₂ := b8e196 x y
               grind)
            | exact superpose b8e196 b8e320
            | (have j1 := b8e196 x y
               grind)
            | (have r₁ := b8e320
               have r₂ := b8e196 x y
               grind)
            | exact resolve b8e320 b8e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e196 b8e320
          have b8e326 : y = (M.op x y) := by grind
          clear b8e325
          have b8e328 : False := by grind
          exact b8e328

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxyy_pyy_pxy_x_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) b = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) b = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) y) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x y) y) = (M.op y y) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) := by grind
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op (M.op x y) y) = (M.op y y) := by grind
        have b1e21 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
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
        have b1e25 : (σ x) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e23
          | exact resolve b1e23 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e30 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) := by
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
        have b1e31 : (M.op x y) = (k x y) := by grind
        clear b1e30
        have b1e33 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e35 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e33
        have b1e36 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e35
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e35
          | exact resolve b1e35 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e37 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e36
             have r₂ := b1e25
             grind)
          | exact resolve b1e36 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e36
        have b1e38 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e37
          | exact resolve b1e37 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e39 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e38
          | exact resolve b1e38 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e38
        have b1e40 : False := by grind
        exact b1e40
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op x y) y) = (M.op y y) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
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
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 (M.op X0 X0) X0
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e56 (σ X1) (σ X0)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e362 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
        clear b2e74
        have b2e371 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e362
             have r₂ := b2e22
             grind)
          | exact resolve b2e362 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e362
        have b2e375 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e371
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e371
          | exact resolve b2e371 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e371
        have b2e376 : False := by grind
        exact b2e376
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op (M.op x y) y) ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) := by grind
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
        have b3e25 : x ≠ (M.op y y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e23
          | exact resolve b3e23 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e42 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e43 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e42
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
        have b3e47 : (σ x) ≠ (σ (k x y)) := by
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
        have b3e49 : x ≠ x ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) := by
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
        have b3e52 : (M.op x y) = (M.op y y) ∨ x = (k x y) := by grind
        clear b3e49
        have b3e54 : x = (M.op y y) ∨ x = (k x y) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e52
          | exact resolve b3e52 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e56 : x = (k x y) := by
          first
          | (have r₁ := b3e54
             have r₂ := b3e25
             grind)
          | exact resolve b3e54 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e54
        have b3e77 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e47
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e47
          | exact resolve b3e47 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e56
        have b3e78 : False := by grind
        exact b3e78
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
          have b4e30 : (σ x) ≠ (σ x) := by
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
          have b4e31 : False := by grind
          exact b4e31
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op (M.op x y) y) ≠ (M.op y y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e27 : x ≠ (M.op y y) := by
            first
            | (have i₁ := b5e25
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e25
            | exact resolve b5e25 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25
          have b5e52 : x ≠ x ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) := by
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
          have b5e53 : (M.op x y) = (M.op y y) ∨ x = (k x y) := by grind
          clear b5e52
          have b5e54 : x = (M.op y y) ∨ x = (k x y) := by
            first
            | (have i₁ := b5e53
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e53
            | exact resolve b5e53 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e55 : x = (k x y) := by
            first
            | (have r₁ := b5e54
               have r₂ := b5e27
               grind)
            | exact resolve b5e54 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e54
          have b5e58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
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
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 (M.op X0 X0) X0
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e62 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e61 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e62 (σ X1) (σ X0)
               grind)
            | exact superpose b5e62 b5e19
            | (have j1 := b5e62 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e334 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e80 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e476 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e334 x y
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e334
            | (have j0 := b5e334 x y
               grind)
            | exact resolve b5e334 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e334
          have b5e480 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e476
          have b5e483 : False := by grind
          exact b5e483
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) := by grind
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
        have b6e53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
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
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 (M.op X0 X0) X0
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e57 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e76 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e57 y x
             grind)
          | exact superpose b6e57 b6e42
          | (have j1 := b6e57 y x
             grind)
          | exact resolve b6e42 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e57
        have b6e77 : x = (M.op x y) := by grind
        clear b6e76
        have b6e78 : False := by grind
        exact b6e78
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
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
          have b7e27 : (σ x) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e25
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e25
            | exact resolve b7e25 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25
          have b7e44 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e45 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e44
          have b7e46 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e45
            | exact resolve b7e45 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e27
               grind)
            | exact resolve b7e46 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27 b7e46
          have b7e48 : (σ x) = (σ (k x y)) := by
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
          have b7e51 : (k x y) = (τ (σ x)) := by
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
          have b7e52 : x = (k x y) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e51
            | exact resolve b7e51 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
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
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 (M.op X0 X0) X0
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e61 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e68 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e61 y x
               grind)
            | exact superpose b7e61 b7e52
            | (have j1 := b7e61 y x
               grind)
            | exact resolve b7e52 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52 b7e61
          have b7e70 : x = (M.op x y) := by grind
          clear b7e68
          have b7e73 : False := by grind
          exact b7e73
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
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
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 (M.op X0 X0) X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e54 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e54 (σ X1) (σ X0)
               grind)
            | exact superpose b8e54 b8e19
            | (have j1 := b8e54 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e54 (τ X1) X0
               grind)
            | exact superpose b8e54 b8e26
            | (have j1 := b8e54 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e54
          have b8e176 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e73 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e73
            | exact resolve b8e73 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e176 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e176
            | (have j0 := b8e176 X0 X1
               grind)
            | exact resolve b8e176 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e176
          have b8e315 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e324 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e315
               have r₂ := b8e24
               grind)
            | exact resolve b8e315 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e315
          have b8e329 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e324
               have i₂ := b8e200 y x
               grind)
            | exact superpose b8e200 b8e324
            | (have j1 := b8e200 y x
               grind)
            | (have r₁ := b8e324
               have r₂ := b8e200 y x
               grind)
            | exact resolve b8e324 b8e200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e200 b8e324
          have b8e330 : x = (M.op x y) := by grind
          clear b8e329
          have b8e332 : False := by grind
          exact b8e332

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),m(X,X)) = m(Y,X) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxpxx_pyx_pyx_x_pyx_x_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) (M.op a a) ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a a)) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) (M.op a a) = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a a)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) (M.op a a) = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a a)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) (M.op x x)) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
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
      have b0e67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X1 X0
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e16 (M.op X1 X1) (M.op X1 X1)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e67 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e72 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e71 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71
      have b0e91 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e72 (τ X0) X1
           grind)
        | exact superpose b0e72 b0e22
        | (have j1 := b0e72 (τ X0) X1
           grind)
        | exact resolve b0e22 b0e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e72 (σ X0) (σ X1)
           grind)
        | exact superpose b0e72 b0e17
        | (have j1 := b0e72 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72
      have b0e376 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e91 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e91
        | exact resolve b0e91 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91
      have b0e407 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e376 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e376
        | (have j0 := b0e376 X0 X1
           grind)
        | exact resolve b0e376 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e376
      have b0e526 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e93 x y
           grind)
        | exact superpose b0e93 b0e18
        | (have j1 := b0e93 x y
           grind)
        | exact resolve b0e18 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e546 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93
      have b0e669 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e526
           have i₂ := b0e407 x y
           grind)
        | exact superpose b0e407 b0e526
        | (have j1 := b0e407 (σ x) (σ y)
           grind)
        | (have r₁ := b0e526
           have r₂ := b0e407 x y
           grind)
        | exact resolve b0e526 b0e407
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e526
      have b0e670 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e669
      have b0e673 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e670
           grind)
        | exact superpose b0e670 b0e18
        | exact resolve b0e18 b0e670
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e674 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e670
           grind)
        | exact superpose b0e670 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e670
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e670
           grind)
        | exact resolve b0e15 b0e670
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e675 : (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e670
           grind)
        | exact superpose b0e670 b0e14
        | exact resolve b0e14 b0e670
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e670
      have b0e676 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
      clear b0e674
      have b0e677 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e675
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e675
        | exact resolve b0e675 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e675
      have b0e678 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e676
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e676
        | exact resolve b0e676 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e676
      have b0e680 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e678
           have r₂ := b0e677
           grind)
        | exact resolve b0e678 b0e677
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e677 b0e678
      have b0e821 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e407 x y
           have i₂ := b0e680
           grind)
        | exact superpose b0e680 b0e407
        | (have j0 := b0e407 x y
           grind)
        | exact resolve b0e407 b0e680
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e407 b0e680
      have b0e844 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e821
      have b0e865 : y = (M.op x y) := by
        first
        | (have r₁ := b0e844
           have r₂ := b0e673
           grind)
        | exact resolve b0e844 b0e673
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e673 b0e844
      have b0e947 : y ≠ y ∨ y = (M.op y (M.op y y)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e865
           grind)
        | exact superpose b0e865 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e865
           grind)
        | exact resolve b0e15 b0e865
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e948 : y ≠ (M.op y (M.op y y)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e865
           grind)
        | exact superpose b0e865 b0e14
        | exact resolve b0e14 b0e865
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e949 : y = (M.op y (M.op y y)) ∨ y = (k y x) := by grind
      clear b0e947
      have b0e950 : y = (k y x) := by
        first
        | (have r₁ := b0e949
           have r₂ := b0e948
           grind)
        | exact resolve b0e949 b0e948
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e948 b0e949
      have b0e1036 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e546 x y
           have i₂ := b0e950
           grind)
        | exact superpose b0e950 b0e546
        | (have j0 := b0e546 x y
           grind)
        | exact resolve b0e546 b0e950
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e546 b0e950
      have b0e1041 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e1036
      have b0e1137 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1041
           grind)
        | exact superpose b0e1041 b0e18
        | exact resolve b0e18 b0e1041
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1041
      have b0e1143 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e1137
           have i₂ := b0e865
           grind)
        | exact superpose b0e865 b0e1137
        | exact resolve b0e1137 b0e865
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e865 b0e1137
      have b0e1144 : False := by grind
      exact b0e1144
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X1 X0
             have i₂ := b1e17 X1 X0
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X1 X0
             have j1 := b1e17 X1 X0
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X1 X1
             have r₂ := b1e17 (M.op X1 X1) (M.op X1 X1)
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e62 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e74 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e25 X0 X1
             have i₂ := b1e62 (τ X0) X1
             grind)
          | exact superpose b1e62 b1e25
          | (have j1 := b1e62 (τ X0) X1
             grind)
          | exact resolve b1e25 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e62 (σ X0) (σ X1)
             grind)
          | exact superpose b1e62 b1e18
          | (have j1 := b1e62 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e275 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e74 (σ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e74
          | exact resolve b1e74 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e300 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e275 X0 X1
             have i₂ := b1e18 X1 X0
             grind)
          | exact superpose b1e18 b1e275
          | (have j0 := b1e275 X0 X1
             grind)
          | exact resolve b1e275 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e275
        have b1e428 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
        have b1e440 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e75 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e428
             have i₂ := b1e300 x y
             grind)
          | exact superpose b1e300 b1e428
          | (have j1 := b1e300 (σ x) (σ y)
             grind)
          | (have r₁ := b1e428
             have r₂ := b1e300 x y
             grind)
          | exact resolve b1e428 b1e300
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e428
        have b1e626 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b1e625
        have b1e629 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e626
             grind)
          | exact superpose b1e626 b1e19
          | exact resolve b1e19 b1e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e630 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e626
             grind)
          | exact superpose b1e626 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e626
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e626
             grind)
          | exact resolve b1e16 b1e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e631 : (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e626
             grind)
          | exact superpose b1e626 b1e15
          | exact resolve b1e15 b1e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e626
        have b1e632 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b1e630
        have b1e633 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e631
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e631
          | exact resolve b1e631 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e631
        have b1e634 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e632
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e632
          | exact resolve b1e632 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e632
        have b1e636 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b1e634
             have r₂ := b1e633
             grind)
          | exact resolve b1e634 b1e633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e633 b1e634
        have b1e706 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e300 x y
             have i₂ := b1e636
             grind)
          | exact superpose b1e636 b1e300
          | (have j0 := b1e300 x y
             grind)
          | exact resolve b1e300 b1e636
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e300 b1e636
        have b1e729 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b1e706
        have b1e750 : y = (M.op x y) := by
          first
          | (have r₁ := b1e729
             have r₂ := b1e629
             grind)
          | exact resolve b1e729 b1e629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e629 b1e729
        have b1e820 : y ≠ y ∨ y = (M.op y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e750
             grind)
          | exact superpose b1e750 b1e16
          | (have j0 := b1e16 y x
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e750
             grind)
          | exact resolve b1e16 b1e750
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e821 : y ≠ (M.op y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e750
             grind)
          | exact superpose b1e750 b1e15
          | exact resolve b1e15 b1e750
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e822 : y = (M.op y (M.op y y)) ∨ y = (k y x) := by grind
        clear b1e820
        have b1e823 : y = (k y x) := by
          first
          | (have r₁ := b1e822
             have r₂ := b1e821
             grind)
          | exact resolve b1e822 b1e821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e821 b1e822
        have b1e901 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e440 x y
             have i₂ := b1e823
             grind)
          | exact superpose b1e823 b1e440
          | (have j0 := b1e440 x y
             grind)
          | exact resolve b1e440 b1e823
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e440 b1e823
        have b1e905 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b1e901
        have b1e987 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e905
             grind)
          | exact superpose b1e905 b1e19
          | exact resolve b1e19 b1e905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e905
        have b1e993 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e987
             have i₂ := b1e750
             grind)
          | exact superpose b1e750 b1e987
          | exact resolve b1e987 b1e750
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e750 b1e987
        have b1e994 : False := by grind
        exact b1e994
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
        have b2e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e58 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e75 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e24 X0 X1
             have i₂ := b2e58 (τ X0) X1
             grind)
          | exact superpose b2e58 b2e24
          | (have j1 := b2e58 (τ X0) X1
             grind)
          | exact resolve b2e24 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e58 (σ X0) (σ X1)
             grind)
          | exact superpose b2e58 b2e18
          | (have j1 := b2e58 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e250 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e75 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e75
          | exact resolve b2e75 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e277 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e250 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e250
          | (have j0 := b2e250 X0 X1
             grind)
          | exact resolve b2e250 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e250
        have b2e410 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
        have b2e422 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e77 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e569 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e410
             have i₂ := b2e277 x y
             grind)
          | exact superpose b2e277 b2e410
          | (have j1 := b2e277 (σ x) (σ y)
             grind)
          | (have r₁ := b2e410
             have r₂ := b2e277 x y
             grind)
          | exact resolve b2e410 b2e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e410
        have b2e570 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b2e569
        have b2e573 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e570
             grind)
          | exact superpose b2e570 b2e19
          | exact resolve b2e19 b2e570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e574 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e16 (σ y) (σ x)
             have i₂ := b2e570
             grind)
          | exact superpose b2e570 b2e16
          | (have j0 := b2e16 (σ y) (σ x)
             grind)
          | (have r₁ := b2e16 (σ y) (σ x)
             have r₂ := b2e570
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e570
             grind)
          | exact resolve b2e16 b2e570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e575 : (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e15 (σ y) (σ x)
             have i₂ := b2e570
             grind)
          | exact superpose b2e570 b2e15
          | exact resolve b2e15 b2e570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e570
        have b2e576 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b2e574
        have b2e577 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e575
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e575
          | exact resolve b2e575 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e575
        have b2e578 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e576
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e576
          | exact resolve b2e576 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e576
        have b2e580 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b2e578
             have r₂ := b2e577
             grind)
          | exact resolve b2e578 b2e577
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e577 b2e578
        have b2e715 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e277 x y
             have i₂ := b2e580
             grind)
          | exact superpose b2e580 b2e277
          | (have j0 := b2e277 x y
             grind)
          | exact resolve b2e277 b2e580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277 b2e580
        have b2e739 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b2e715
        have b2e760 : y = (M.op x y) := by
          first
          | (have r₁ := b2e739
             have r₂ := b2e573
             grind)
          | exact resolve b2e739 b2e573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e573 b2e739
        have b2e839 : y ≠ y ∨ y = (M.op y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e760
             grind)
          | exact superpose b2e760 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e760
             grind)
          | exact resolve b2e16 b2e760
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e840 : y ≠ (M.op y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e760
             grind)
          | exact superpose b2e760 b2e15
          | exact resolve b2e15 b2e760
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e841 : y = (M.op y (M.op y y)) ∨ y = (k y x) := by grind
        clear b2e839
        have b2e842 : y = (k y x) := by
          first
          | (have r₁ := b2e841
             have r₂ := b2e840
             grind)
          | exact resolve b2e841 b2e840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e840 b2e841
        have b2e925 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e422 x y
             have i₂ := b2e842
             grind)
          | exact superpose b2e842 b2e422
          | (have j0 := b2e422 x y
             grind)
          | exact resolve b2e422 b2e842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e422 b2e842
        have b2e929 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e925
        have b2e1022 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e929
             grind)
          | exact superpose b2e929 b2e19
          | exact resolve b2e19 b2e929
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e929
        have b2e1028 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1022
             have i₂ := b2e760
             grind)
          | exact superpose b2e760 b2e1022
          | exact resolve b2e1022 b2e760
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e760 b2e1022
        have b2e1029 : False := by grind
        exact b2e1029
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X1 X0
             have i₂ := b3e17 X1 X0
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X1 X0
             have j1 := b3e17 X1 X0
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 (M.op X1 X1) (M.op X1 X1)
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e65 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e82 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e25 X0 X1
             have i₂ := b3e65 (τ X0) X1
             grind)
          | exact superpose b3e65 b3e25
          | (have j1 := b3e65 (τ X0) X1
             grind)
          | exact resolve b3e25 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e65 (σ X0) (σ X1)
             grind)
          | exact superpose b3e65 b3e18
          | (have j1 := b3e65 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e260 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e82 (σ X0) X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e82
          | exact resolve b3e82 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e283 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e260 X0 X1
             have i₂ := b3e18 X1 X0
             grind)
          | exact superpose b3e18 b3e260
          | (have j0 := b3e260 X0 X1
             grind)
          | exact resolve b3e260 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e260
        have b3e371 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e84 x y
             grind)
          | exact superpose b3e84 b3e19
          | (have j1 := b3e84 x y
             grind)
          | exact resolve b3e19 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e390 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e84 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e676 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e371
             have i₂ := b3e283 x y
             grind)
          | exact superpose b3e283 b3e371
          | (have j1 := b3e283 (σ x) (σ y)
             grind)
          | (have r₁ := b3e371
             have r₂ := b3e283 x y
             grind)
          | exact resolve b3e371 b3e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e371
        have b3e677 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b3e676
        have b3e736 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e677
             grind)
          | exact superpose b3e677 b3e19
          | exact resolve b3e19 b3e677
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e737 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e677
             grind)
          | exact superpose b3e677 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | (have r₁ := b3e16 (σ y) (σ x)
             have r₂ := b3e677
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e677
             grind)
          | exact resolve b3e16 b3e677
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e738 : (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e677
             grind)
          | exact superpose b3e677 b3e15
          | exact resolve b3e15 b3e677
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e677
        have b3e739 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b3e737
        have b3e740 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e738
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e738
          | exact resolve b3e738 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e738
        have b3e741 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e739
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e739
          | exact resolve b3e739 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e739
        have b3e743 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b3e741
             have r₂ := b3e740
             grind)
          | exact resolve b3e741 b3e740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e740 b3e741
        have b3e828 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e283 x y
             have i₂ := b3e743
             grind)
          | exact superpose b3e743 b3e283
          | (have j0 := b3e283 x y
             grind)
          | exact resolve b3e283 b3e743
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e283 b3e743
        have b3e851 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b3e828
        have b3e872 : y = (M.op x y) := by
          first
          | (have r₁ := b3e851
             have r₂ := b3e736
             grind)
          | exact resolve b3e851 b3e736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e736 b3e851
        have b3e943 : y ≠ y ∨ y = (M.op y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e872
             grind)
          | exact superpose b3e872 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e872
             grind)
          | exact resolve b3e16 b3e872
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e944 : y ≠ (M.op y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e872
             grind)
          | exact superpose b3e872 b3e15
          | exact resolve b3e15 b3e872
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e945 : y = (M.op y (M.op y y)) ∨ y = (k y x) := by grind
        clear b3e943
        have b3e946 : y = (k y x) := by
          first
          | (have r₁ := b3e945
             have r₂ := b3e944
             grind)
          | exact resolve b3e945 b3e944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e944 b3e945
        have b3e1025 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e390 x y
             have i₂ := b3e946
             grind)
          | exact superpose b3e946 b3e390
          | (have j0 := b3e390 x y
             grind)
          | exact resolve b3e390 b3e946
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e390 b3e946
        have b3e1029 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b3e1025
        have b3e1111 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1029
             grind)
          | exact superpose b3e1029 b3e19
          | exact resolve b3e19 b3e1029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1029
        have b3e1117 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e1111
             have i₂ := b3e872
             grind)
          | exact superpose b3e872 b3e1111
          | exact resolve b3e1111 b3e872
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e872 b3e1111
        have b3e1118 : False := by grind
        exact b3e1118
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 (M.op X1 X1) (M.op X1 X1)
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e68 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e57 (τ X0) X1
               grind)
            | exact superpose b4e57 b4e28
            | (have j1 := b4e57 (τ X0) X1
               grind)
            | exact resolve b4e28 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e57 (σ X0) (σ X1)
               grind)
            | exact superpose b4e57 b4e19
            | (have j1 := b4e57 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e191 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e68 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e68
            | exact resolve b4e68 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e214 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e191 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e191
            | (have j0 := b4e191 X0 X1
               grind)
            | exact resolve b4e191 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191
          have b4e331 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e70 x y
               grind)
            | exact superpose b4e70 b4e20
            | (have j1 := b4e70 x y
               grind)
            | exact resolve b4e20 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e342 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e70 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e331
               have i₂ := b4e214 x y
               grind)
            | exact superpose b4e214 b4e331
            | (have j1 := b4e214 (σ x) (σ y)
               grind)
            | (have r₁ := b4e331
               have r₂ := b4e214 x y
               grind)
            | exact resolve b4e331 b4e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e331
          have b4e567 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b4e566
          have b4e570 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e567
               grind)
            | exact superpose b4e567 b4e20
            | exact resolve b4e20 b4e567
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e571 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e567
               grind)
            | exact superpose b4e567 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e567
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e567
               grind)
            | exact resolve b4e17 b4e567
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e572 : (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e567
               grind)
            | exact superpose b4e567 b4e16
            | exact resolve b4e16 b4e567
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e567
          have b4e573 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b4e571
          have b4e574 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e572
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e572
            | exact resolve b4e572 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e572
          have b4e575 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e573
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e573
            | exact resolve b4e573 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e573
          have b4e577 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e575
               have r₂ := b4e574
               grind)
            | exact resolve b4e575 b4e574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e574 b4e575
          have b4e648 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e214 x y
               have i₂ := b4e577
               grind)
            | exact superpose b4e577 b4e214
            | (have j0 := b4e214 x y
               grind)
            | exact resolve b4e214 b4e577
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214 b4e577
          have b4e672 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b4e648
          have b4e693 : y = (M.op x y) := by
            first
            | (have r₁ := b4e672
               have r₂ := b4e570
               grind)
            | exact resolve b4e672 b4e570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e570 b4e672
          have b4e764 : y ≠ y ∨ y = (M.op y (M.op y y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e693
               grind)
            | exact superpose b4e693 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e693
               grind)
            | exact resolve b4e17 b4e693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e765 : y ≠ (M.op y (M.op y y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e693
               grind)
            | exact superpose b4e693 b4e16
            | exact resolve b4e16 b4e693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e766 : y = (M.op y (M.op y y)) ∨ y = (k y x) := by grind
          clear b4e764
          have b4e767 : y = (k y x) := by
            first
            | (have r₁ := b4e766
               have r₂ := b4e765
               grind)
            | exact resolve b4e766 b4e765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e765 b4e766
          have b4e846 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e342 x y
               have i₂ := b4e767
               grind)
            | exact superpose b4e767 b4e342
            | (have j0 := b4e342 x y
               grind)
            | exact resolve b4e342 b4e767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342 b4e767
          have b4e850 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b4e846
          have b4e933 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e850
               grind)
            | exact superpose b4e850 b4e20
            | exact resolve b4e20 b4e850
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e850
          have b4e939 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e933
               have i₂ := b4e693
               grind)
            | exact superpose b4e693 b4e933
            | exact resolve b4e933 b4e693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e693 b4e933
          have b4e940 : False := by grind
          exact b4e940
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op (M.op y x) (M.op x x)) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ (M.op x (M.op x x)) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : x ≠ x ∨ x = (M.op x (M.op x x)) ∨ x = (k x y) := by
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
          have b5e42 : x = (M.op x (M.op x x)) ∨ x = (k x y) := by grind
          clear b5e41
          have b5e43 : x = (k x y) := by
            first
            | (have r₁ := b5e42
               have r₂ := b5e25
               grind)
            | exact resolve b5e42 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e42
          have b5e47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
          have b5e51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e52 (σ X0) (σ X1)
               grind)
            | exact superpose b5e52 b5e19
            | (have j1 := b5e52 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e339 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e66 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e479 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e339 y x
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e339
            | (have j0 := b5e339 y x
               grind)
            | exact resolve b5e339 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e339
          have b5e483 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e479
          have b5e486 : False := by grind
          exact b5e486
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b6e61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
        have b6e65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e66 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e66 (σ X0) (σ X1)
             grind)
          | exact superpose b6e66 b6e18
          | (have j1 := b6e66 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e88 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X0 X1
             have i₂ := b6e66 (τ X0) X1
             grind)
          | exact superpose b6e66 b6e24
          | (have j1 := b6e66 (τ X0) X1
             grind)
          | exact resolve b6e24 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e66
        have b6e257 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e88 (σ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e88
          | exact resolve b6e88 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e257 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e257
          | (have j0 := b6e257 X0 X1
             grind)
          | exact resolve b6e257 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e257
        have b6e407 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e85 x y
             grind)
          | exact superpose b6e85 b6e19
          | (have j1 := b6e85 x y
             grind)
          | exact resolve b6e19 b6e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e425 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e85 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e656 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e407
             have i₂ := b6e282 x y
             grind)
          | exact superpose b6e282 b6e407
          | (have j1 := b6e282 (σ x) (σ y)
             grind)
          | (have r₁ := b6e407
             have r₂ := b6e282 x y
             grind)
          | exact resolve b6e407 b6e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e407
        have b6e657 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b6e656
        have b6e660 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e657
             grind)
          | exact superpose b6e657 b6e19
          | exact resolve b6e19 b6e657
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e661 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e657
             grind)
          | exact superpose b6e657 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e657
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e657
             grind)
          | exact resolve b6e16 b6e657
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e662 : (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e657
             grind)
          | exact superpose b6e657 b6e15
          | exact resolve b6e15 b6e657
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e657
        have b6e663 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b6e661
        have b6e664 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e662
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e662
          | exact resolve b6e662 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e662
        have b6e665 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e663
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e663
          | exact resolve b6e663 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e663
        have b6e667 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e665
             have r₂ := b6e664
             grind)
          | exact resolve b6e665 b6e664
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e664 b6e665
        have b6e802 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e282 x y
             have i₂ := b6e667
             grind)
          | exact superpose b6e667 b6e282
          | (have j0 := b6e282 x y
             grind)
          | exact resolve b6e282 b6e667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e282 b6e667
        have b6e826 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b6e802
        have b6e847 : y = (M.op x y) := by
          first
          | (have r₁ := b6e826
             have r₂ := b6e660
             grind)
          | exact resolve b6e826 b6e660
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e660 b6e826
        have b6e926 : y ≠ y ∨ y = (M.op y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e847
             grind)
          | exact superpose b6e847 b6e16
          | (have j0 := b6e16 y x
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e847
             grind)
          | exact resolve b6e16 b6e847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e927 : y ≠ (M.op y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e847
             grind)
          | exact superpose b6e847 b6e15
          | exact resolve b6e15 b6e847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e928 : y = (M.op y (M.op y y)) ∨ y = (k y x) := by grind
        clear b6e926
        have b6e929 : y = (k y x) := by
          first
          | (have r₁ := b6e928
             have r₂ := b6e927
             grind)
          | exact resolve b6e928 b6e927
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e927 b6e928
        have b6e1012 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e425 x y
             have i₂ := b6e929
             grind)
          | exact superpose b6e929 b6e425
          | (have j0 := b6e425 x y
             grind)
          | exact resolve b6e425 b6e929
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e425 b6e929
        have b6e1016 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b6e1012
        have b6e1109 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e1016
             grind)
          | exact superpose b6e1016 b6e19
          | exact resolve b6e19 b6e1016
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1016
        have b6e1115 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b6e1109
             have i₂ := b6e847
             grind)
          | exact superpose b6e847 b6e1109
          | exact resolve b6e1109 b6e847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e847 b6e1109
        have b6e1116 : False := by grind
        exact b6e1116
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e62 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e61
          have b7e63 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e25
               grind)
            | exact resolve b7e62 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e62
          have b7e64 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e63
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e63
            | exact resolve b7e63 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e69 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e14
            | exact resolve b7e14 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
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
          have b7e78 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          have b7e82 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e83 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e82 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e93 : x = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e83 y x
               grind)
            | exact superpose b7e83 b7e70
            | (have j1 := b7e83 y x
               grind)
            | exact resolve b7e70 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e83
          have b7e95 : x = (M.op y x) := by grind
          clear b7e93
          have b7e98 : False := by grind
          exact b7e98
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e73 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          have b8e77 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e78 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e78 (σ X0) (σ X1)
               grind)
            | exact superpose b8e78 b8e19
            | (have j1 := b8e78 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e88 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e78 (τ X0) X1
               grind)
            | exact superpose b8e78 b8e26
            | (have j1 := b8e78 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e78
          have b8e210 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e88 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e88
            | exact resolve b8e88 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e235 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e210 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e210
            | (have j0 := b8e210 X0 X1
               grind)
            | exact resolve b8e210 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210
          have b8e359 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e84 x y
               grind)
            | exact superpose b8e84 b8e20
            | (have j1 := b8e84 x y
               grind)
            | exact resolve b8e20 b8e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e371 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e84 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e558 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e359
               have i₂ := b8e235 x y
               grind)
            | exact superpose b8e235 b8e359
            | (have j1 := b8e235 (σ x) (σ y)
               grind)
            | (have r₁ := b8e359
               have r₂ := b8e235 x y
               grind)
            | exact resolve b8e359 b8e235
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e359
          have b8e559 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b8e558
          have b8e562 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e559
               grind)
            | exact superpose b8e559 b8e20
            | exact resolve b8e20 b8e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e563 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e559
               grind)
            | exact superpose b8e559 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e559
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e559
               grind)
            | exact resolve b8e17 b8e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e564 : (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e559
               grind)
            | exact superpose b8e559 b8e16
            | exact resolve b8e16 b8e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e559
          have b8e565 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e563
          have b8e566 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e564
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e564
            | exact resolve b8e564 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e564
          have b8e567 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e565
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e565
            | exact resolve b8e565 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e565
          have b8e569 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e567
               have r₂ := b8e566
               grind)
            | exact resolve b8e567 b8e566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e566 b8e567
          have b8e704 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e235 x y
               have i₂ := b8e569
               grind)
            | exact superpose b8e569 b8e235
            | (have j0 := b8e235 x y
               grind)
            | exact resolve b8e235 b8e569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e235 b8e569
          have b8e728 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b8e704
          have b8e749 : y = (M.op x y) := by
            first
            | (have r₁ := b8e728
               have r₂ := b8e562
               grind)
            | exact resolve b8e728 b8e562
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e562 b8e728
          have b8e828 : y ≠ y ∨ y = (M.op y (M.op y y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e749
               grind)
            | exact superpose b8e749 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e749
               grind)
            | exact resolve b8e17 b8e749
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e829 : y ≠ (M.op y (M.op y y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e749
               grind)
            | exact superpose b8e749 b8e16
            | exact resolve b8e16 b8e749
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e830 : y = (M.op y (M.op y y)) ∨ y = (k y x) := by grind
          clear b8e828
          have b8e831 : y = (k y x) := by
            first
            | (have r₁ := b8e830
               have r₂ := b8e829
               grind)
            | exact resolve b8e830 b8e829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e829 b8e830
          have b8e914 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e371 x y
               have i₂ := b8e831
               grind)
            | exact superpose b8e831 b8e371
            | (have j0 := b8e371 x y
               grind)
            | exact resolve b8e371 b8e831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e371 b8e831
          have b8e918 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e914
          have b8e1011 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e918
               grind)
            | exact superpose b8e918 b8e20
            | exact resolve b8e20 b8e918
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e918
          have b8e1017 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e1011
               have i₂ := b8e749
               grind)
            | exact superpose b8e749 b8e1011
            | exact resolve b8e1011 b8e749
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e749 b8e1011
          have b8e1018 : False := by grind
          exact b8e1018

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),m(X,X)) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxpxx_x_pxy_x_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 0))) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 0))) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) (M.op a a) ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a a)) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) (M.op a a) = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a a)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) (M.op a a) = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a a)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) (M.op x x)) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op (M.op y x) (M.op x x)) := by grind
      have b0e20 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
      have b0e30 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op (M.op y x) (M.op x x)) := by grind
        have b1e21 : (σ x) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
        have b1e41 : (M.op x y) = (k x y) := by grind
        clear b1e40
        have b1e43 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e45 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e46 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e45
             have r₂ := b1e21
             grind)
          | exact resolve b1e45 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e47 : (σ x) = (σ (k x y)) := by
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
        have b1e48 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e47
          | exact resolve b1e47 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e47
        have b1e49 : False := by grind
        exact b1e49
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op (M.op y x) (M.op x x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
        have b2e53 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b2e57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e58 (σ X0) (σ X1)
             grind)
          | exact superpose b2e58 b2e18
          | (have j1 := b2e58 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e364 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
        clear b2e77
        have b2e379 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e364
             have r₂ := b2e22
             grind)
          | exact resolve b2e364 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e364
        have b2e383 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e379
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e379
          | exact resolve b2e379 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e379
        have b2e384 : False := by grind
        exact b2e384
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op (M.op y x) (M.op x x)) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e40
        have b3e42 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b3e43 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e23
          | exact resolve b3e23 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e42
        have b3e46 : x ≠ x ∨ x = (M.op (M.op y x) (M.op x x)) ∨ x = (k x y) := by
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
        have b3e49 : x = (M.op (M.op y x) (M.op x x)) ∨ x = (k x y) := by grind
        clear b3e46
        have b3e50 : x = (k x y) := by
          first
          | (have r₁ := b3e49
             have r₂ := b3e20
             grind)
          | exact resolve b3e49 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e67 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e43
          | exact resolve b3e43 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e50
        have b3e68 : False := by grind
        exact b3e68
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : False := by grind
          exact b4e27
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op (M.op y x) (M.op x x)) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e49 : x ≠ x ∨ x = (M.op (M.op y x) (M.op x x)) ∨ x = (k x y) := by
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
          have b5e50 : x = (M.op (M.op y x) (M.op x x)) ∨ x = (k x y) := by grind
          clear b5e49
          have b5e51 : x = (k x y) := by
            first
            | (have r₁ := b5e50
               have r₂ := b5e21
               grind)
            | exact resolve b5e50 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b5e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e61 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e62 (σ X0) (σ X1)
               grind)
            | exact superpose b5e62 b5e19
            | (have j1 := b5e62 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e84 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e483 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e344 x y
               have i₂ := b5e51
               grind)
            | exact superpose b5e51 b5e344
            | (have j0 := b5e344 x y
               grind)
            | exact resolve b5e344 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e344
          have b5e487 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e483
          have b5e490 : False := by grind
          exact b5e490
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ((σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e41 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b6e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b6e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e73 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e56 x y
             grind)
          | exact superpose b6e56 b6e41
          | (have j1 := b6e56 x y
             grind)
          | exact resolve b6e41 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e56
        have b6e74 : x = (M.op x y) := by grind
        clear b6e73
        have b6e75 : False := by grind
        exact b6e75
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e43 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e44 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e23
               grind)
            | exact resolve b7e43 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
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
          have b7e57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b7e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e61 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e72 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e62 x y
               grind)
            | exact superpose b7e62 b7e49
            | (have j1 := b7e62 x y
               grind)
            | exact resolve b7e49 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49 b7e62
          have b7e74 : x = (M.op x y) := by grind
          clear b7e72
          have b7e77 : False := by grind
          exact b7e77
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e56 (σ X0) (σ X1)
               grind)
            | exact superpose b8e56 b8e19
            | (have j1 := b8e56 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e56 X0 (τ X1)
               grind)
            | exact superpose b8e56 b8e26
            | (have j1 := b8e56 X0 (τ X1)
               grind)
            | exact resolve b8e26 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e56
          have b8e211 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e77
            | exact resolve b8e77 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e236 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e211 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e211
            | (have j0 := b8e211 X0 X1
               grind)
            | exact resolve b8e211 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211
          have b8e358 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          clear b8e74
          have b8e373 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e358
               have r₂ := b8e24
               grind)
            | exact resolve b8e358 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358
          have b8e378 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e373
               have i₂ := b8e236 y x
               grind)
            | exact superpose b8e236 b8e373
            | (have j1 := b8e236 y x
               grind)
            | (have r₁ := b8e373
               have r₂ := b8e236 y x
               grind)
            | exact resolve b8e373 b8e236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e236 b8e373
          have b8e379 : x = (M.op x y) := by grind
          clear b8e378
          have b8e381 : False := by grind
          exact b8e381
