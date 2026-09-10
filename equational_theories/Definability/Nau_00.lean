import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e35 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
      have b0e36 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e39 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e36
      have b0e40 : (M.op x y) = (k x y) := by grind
      clear b0e35
      have b0e41 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e39
        | exact resolve b0e39 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e42 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e41
           have i₂ := b0e40
           grind)
        | exact superpose b0e40 b0e41
        | exact resolve b0e41 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e41
      have b0e43 : False := by grind
      exact b0e43
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
        have b1e39 : (M.op x y) = (k x y) := by grind
        clear b1e34
        have b1e42 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e45 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e42
        have b1e47 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e45
             have r₂ := b1e21
             grind)
          | exact resolve b1e45 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e48 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e48
          | exact resolve b1e48 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e48
        have b1e50 : False := by grind
        exact b1e50
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e25 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) y)) = X0 := by
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
        have b2e27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X0 (M.op X2 (M.op X0 X2))
             have i₂ := b2e12 X0 X2 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op (M.op x x) y) X0) X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (M.op (M.op x x) y) X0
             have i₂ := b2e25 X0
             grind)
          | exact superpose b2e25 b2e12
          | exact resolve b2e12 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
        have b2e33 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) X2) ≠ X0 ∨ (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 (M.op (M.op X1 (M.op X2 X1)) X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op (M.op X1 (M.op X2 X1)) X2) X0
             grind)
          | (have r₁ := b2e15 (M.op (M.op X1 (M.op X2 X1)) X2) (M.op (M.op X1 (M.op X2 X1)) X2)
             have r₂ := b2e12 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : (M.op x y) = (k x y) := by grind
        clear b2e32
        have b2e36 : x ≠ x ∨ y = (M.op x y) ∨ x = (k y x) := by
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
        have b2e39 : x = (k y x) ∨ y = (M.op x y) := by grind
        clear b2e36
        have b2e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e53 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e23 X0 X1
             grind)
          | exact superpose b2e23 b2e13
          | exact resolve b2e13 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e81 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e53 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e53
          | exact resolve b2e53 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e225 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X0) (σ X1)
             have i₂ := b2e47 X1 X0
             grind)
          | exact superpose b2e47 b2e15
          | (have j0 := b2e15 (σ X0) (σ X1)
             have j1 := b2e47 X1 X0
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e47 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X1) (σ X0)
             have r₂ := b2e47 X0 X1
             grind)
          | exact resolve b2e15 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e227 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e47 x y
             grind)
          | exact superpose b2e47 b2e21
          | (have j1 := b2e47 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e47 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e47 y x
             grind)
          | exact resolve b2e21 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e232 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X0) (σ X1)
             have i₂ := b2e47 X0 X1
             grind)
          | exact superpose b2e47 b2e15
          | (have j0 := b2e15 (σ X0) (σ X1)
             have j1 := b2e47 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e47 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X1) (σ X0)
             have r₂ := b2e47 X0 X1
             grind)
          | exact resolve b2e15 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e235 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e47 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e237 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e232 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e232
        have b2e240 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e227
        have b2e243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e237 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e237
          | (have j0 := b2e237 X0 X1
             grind)
          | exact resolve b2e237 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e237
        have b2e245 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e240
             have r₂ := b2e22
             grind)
          | exact resolve b2e240 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e240
        have b2e246 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e225 X0 X1
             have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b2e225 X0 X1
             have r₂ := b2e15 (σ X1) (σ X0)
             grind)
          | (have r₁ := b2e225 X0 X1
             have r₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e225 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e225
        have b2e251 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e246 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e246
          | (have j0 := b2e246 X0 X1
             grind)
          | exact resolve b2e246 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e246
        have b2e256 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ (k y x))))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27 (σ x) X0 (σ y)
             have i₂ := b2e245
             grind)
          | exact superpose b2e245 b2e27
          | exact resolve b2e27 b2e245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e284 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1)) = (k (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e33 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e285 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X1) = (k (M.op (M.op X0 (M.op X1 X0)) X1) (M.op (M.op X0 (M.op X1 X0)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e284 X0 X1
             have i₂ := b2e12 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
             grind)
          | exact superpose b2e12 b2e284
          | exact resolve b2e284 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e284
        have b2e605 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ y = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b2e256 X0
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e256
          | exact resolve b2e256 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39
        have b2e5149 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b2e27 (σ y) X0 (σ x)
             have i₂ := b2e605 (σ y)
             grind)
          | exact superpose b2e605 b2e27
          | exact resolve b2e27 b2e605
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e605
        have b2e5758 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x x) y) (σ y))) = X0 ∨ y = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b2e30 (σ y) X0
             have i₂ := b2e5149 (M.op (M.op (M.op x x) y) (σ y))
             grind)
          | exact superpose b2e5149 b2e30
          | exact resolve b2e30 b2e5149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e5149
        have b2e14064 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e235 y x
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e235
          | (have j0 := b2e235 y x
             grind)
          | exact resolve b2e235 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e235
        have b2e14073 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e14064
             have r₂ := b2e22
             grind)
          | exact resolve b2e14064 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14064
        have b2e14077 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have r₁ := b2e14073
             have r₂ := b2e21
             grind)
          | exact resolve b2e14073 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14073
        have b2e14151 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e285 x (M.op X1 (M.op x X1))
             have i₂ := b2e12 x X1 x
             grind)
          | exact superpose b2e12 b2e285
          | exact resolve b2e285 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e14170 : (M.op y (M.op x x)) = (k (M.op y (M.op x x)) (M.op y (M.op x x))) := by
          first
          | (have i₁ := b2e285 y (M.op x x)
             have i₂ := b2e25 y
             grind)
          | exact superpose b2e25 b2e285
          | exact resolve b2e285 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e14400 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e251 (τ X1) (τ X0)
             have i₂ := b2e81 X0 X1
             grind)
          | exact superpose b2e81 b2e251
          | (have j0 := b2e251 (τ X0) (τ X1)
             grind)
          | exact resolve b2e251 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81
        have b2e14419 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e14400 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e14400
          | (have j0 := b2e14400 X0 X1
             grind)
          | exact resolve b2e14400 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14400
        have b2e14422 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e14419 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e14419
          | (have j0 := b2e14419 X0 X1
             grind)
          | exact resolve b2e14419 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14419
        have b2e14424 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e14422 X0 X1
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e14422
          | (have j0 := b2e14422 X0 X1
             grind)
          | exact resolve b2e14422 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14422
        have b2e14425 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e14424 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e14424
          | (have j0 := b2e14424 X0 X1
             grind)
          | exact resolve b2e14424 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14424
        have b2e14426 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e14425 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e14425
          | (have j0 := b2e14425 X0 X1
             grind)
          | exact resolve b2e14425 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14425
        have b2e14427 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e14426 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e14426
          | (have j0 := b2e14426 X0 X1
             grind)
          | exact resolve b2e14426 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14426
        have b2e14428 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e14427 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e14427
          | (have j0 := b2e14427 X0 X1
             grind)
          | exact resolve b2e14427 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14427
        have b2e14714 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e243 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e243
          | exact resolve b2e243 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e243
        have b2e14804 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e14714 X0 X1
             have i₂ := b2e23 X0 X1
             grind)
          | exact superpose b2e23 b2e14714
          | (have j0 := b2e14714 X0 X1
             grind)
          | exact resolve b2e14714 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e14714
        have b2e14811 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e14804 X0 X1
             have i₂ := b2e24 X0 X1
             grind)
          | exact superpose b2e24 b2e14804
          | (have j0 := b2e14804 X0 X1
             grind)
          | exact resolve b2e14804 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14804
        have b2e17469 : (σ (M.op y (M.op x x))) ≠ (σ (M.op y (M.op x x))) ∨ (σ (M.op y (M.op x x))) = (M.op (σ (M.op y (M.op x x))) (σ (M.op y (M.op x x)))) ∨ (σ (M.op y (M.op x x))) = (M.op (σ (M.op y (M.op x x))) (σ (M.op y (M.op x x)))) := by
          first
          | (have i₁ := b2e251 (M.op y (M.op x x)) (M.op y (M.op x x))
             have i₂ := b2e14170
             grind)
          | exact superpose b2e14170 b2e251
          | (have j0 := b2e251 (M.op y (M.op x x)) (M.op y (M.op x x))
             grind)
          | exact resolve b2e251 b2e14170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e251
        have b2e17473 : (σ (M.op y (M.op x x))) ≠ (σ (M.op y (M.op x x))) ∨ (σ (M.op y (M.op x x))) = (M.op (σ (M.op y (M.op x x))) (σ (M.op y (M.op x x)))) := by grind
        clear b2e17469
        have b2e17474 : (σ (M.op y (M.op x x))) = (M.op (σ (M.op y (M.op x x))) (σ (M.op y (M.op x x)))) := by grind
        clear b2e17473
        have b2e18843 : (M.op (σ y) (M.op (M.op x x) y)) = (k (M.op (σ y) (M.op (M.op x x) y)) (M.op (σ y) (M.op (M.op x x) y))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e285 (σ y) (M.op (M.op x x) y)
             have i₂ := b2e5758 (σ y)
             grind)
          | exact superpose b2e5758 b2e285
          | exact resolve b2e285 b2e5758
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e285 b2e5758
        have b2e19035 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e18843
             have i₂ := b2e25 (σ y)
             grind)
          | exact superpose b2e25 b2e18843
          | exact resolve b2e18843 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18843
        have b2e19053 : (σ y) = (σ (k y y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e19035
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e19035
          | exact resolve b2e19035 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19035
        have b2e19293 : (k y y) = (τ (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e13 (k y y)
             have i₂ := b2e19053
             grind)
          | exact superpose b2e19053 b2e13
          | exact resolve b2e13 b2e19053
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19053
        have b2e19362 : y = (k y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e19293
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e19293
          | exact resolve b2e19293 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19293
        have b2e19517 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e14428 y y
             have i₂ := b2e19362
             grind)
          | exact superpose b2e19362 b2e14428
          | (have j0 := b2e14428 y y
             grind)
          | (have r₁ := b2e14428 y y
             have r₂ := b2e19362
             grind)
          | exact resolve b2e14428 b2e19362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14428 b2e19362
        have b2e19518 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
        clear b2e19517
        have b2e19519 : y = (M.op y y) ∨ y = (M.op x y) := by grind
        clear b2e19518
        have b2e19649 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ y = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y y
             have i₂ := b2e19519
             grind)
          | exact superpose b2e19519 b2e12
          | exact resolve b2e12 b2e19519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e20090 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b2e19649 X0
             have i₂ := b2e19519
             grind)
          | exact superpose b2e19519 b2e19649
          | exact resolve b2e19649 b2e19519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19649
        have b2e20277 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ y = (M.op x y) := by
          intro X0
          first
          | (have j0 := b2e20090 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20090
        have b2e20775 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b2e20277 X0
             have i₂ := b2e19519
             grind)
          | exact superpose b2e19519 b2e20277
          | exact resolve b2e20277 b2e19519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19519 b2e20277
        have b2e20967 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) := by
          intro X0
          first
          | (have j0 := b2e20775 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20775
        have b2e21616 : ∀ X0 : G, y ≠ y ∨ (M.op y x) = (k y x) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e20967 X0
             grind)
          | exact superpose b2e20967 b2e15
          | (have j0 := b2e15 y x
             have j1 := b2e20967 X0
             grind)
          | (have r₁ := b2e15 y y
             have r₂ := b2e20967 y
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e20967 X0
             grind)
          | exact resolve b2e15 b2e20967
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20967
        have b2e21648 : ∀ X0 : G, (M.op y x) = (k y x) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e21616 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21616
        have b2e21656 : ∀ X0 : G, x = (k y x) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e21648 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e21648
          | (have j0 := b2e21648 X0
             grind)
          | exact resolve b2e21648 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21648
        have b2e22938 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 ∨ x = (k y x) := by
          intro X0
          first
          | (have i₁ := b2e25 X0
             have i₂ := b2e21656 (M.op x x)
             grind)
          | exact superpose b2e21656 b2e25
          | exact resolve b2e25 b2e21656
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e21656
        have b2e77441 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e14811 (σ X0) X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14811
        have b2e77442 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e77441 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77441
        have b2e77457 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e77442 X0
             have j1 := b2e15 (σ X0) (σ X0)
             grind)
          | (have r₁ := b2e77442 X0
             have r₂ := b2e15 (σ X0) (σ X0)
             grind)
          | exact resolve b2e77442 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77442
        have b2e77498 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e77457 X0
             have i₂ := b2e18 X0 X0
             grind)
          | exact superpose b2e18 b2e77457
          | exact resolve b2e77457 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77457
        have b2e77530 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e77498 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e77498
          | exact resolve b2e77498 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e77575 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) (σ (k X0 X0))) (σ X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (σ X0) (σ X0)
             have i₂ := b2e77498 X0
             grind)
          | exact superpose b2e77498 b2e12
          | exact resolve b2e12 b2e77498
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77498
        have b2e77645 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
          intro X0
          first
          | (have i₁ := b2e77530 X0
             have i₂ := b2e24 X0 (τ X0)
             grind)
          | exact superpose b2e24 b2e77530
          | exact resolve b2e77530 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e77530
        have b2e77650 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e77645 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e77645
          | exact resolve b2e77645 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77645
        have b2e89061 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ (M.op y (M.op x x))) (σ (M.op y (M.op x x)))) (σ (M.op y (M.op x x))))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e77575 (M.op y (M.op x x)) X0
             have i₂ := b2e14170
             grind)
          | exact superpose b2e14170 b2e77575
          | exact resolve b2e77575 b2e14170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14170 b2e77575
        have b2e89921 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op y (M.op x x))) (σ (M.op y (M.op x x))))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e89061 X0
             have i₂ := b2e17474
             grind)
          | exact superpose b2e17474 b2e89061
          | exact resolve b2e89061 b2e17474
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89061
        have b2e90029 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op x x)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e89921 X0
             have i₂ := b2e17474
             grind)
          | exact superpose b2e17474 b2e89921
          | exact resolve b2e89921 b2e17474
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17474 b2e89921
        have b2e92302 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (k y x) := by
          intro X0
          first
          | (have i₁ := b2e90029 X0
             have i₂ := b2e22938 y
             grind)
          | exact superpose b2e22938 b2e90029
          | exact resolve b2e90029 b2e22938
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22938 b2e90029
        have b2e98870 : (σ x) = (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e245
             have i₂ := b2e92302 (σ x)
             grind)
          | exact superpose b2e92302 b2e245
          | exact resolve b2e245 b2e92302
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e245 b2e92302
        have b2e114185 : (k y x) = (τ (σ x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e13 (k y x)
             have i₂ := b2e98870
             grind)
          | exact superpose b2e98870 b2e13
          | exact resolve b2e13 b2e98870
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98870
        have b2e114285 : x = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e114185
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e114185
          | exact resolve b2e114185 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e114185
        have b2e114286 : x = (k y x) := by grind
        clear b2e114285
        have b2e116754 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e256 X0
             have i₂ := b2e114286
             grind)
          | exact superpose b2e114286 b2e256
          | exact resolve b2e256 b2e114286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e256 b2e114286
        have b2e121968 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b2e14151 (σ y) (σ x)
             have i₂ := b2e116754 (σ y)
             grind)
          | exact superpose b2e116754 b2e14151
          | exact resolve b2e14151 b2e116754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14151 b2e116754
        have b2e122751 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b2e121968
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e121968
          | exact resolve b2e121968 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121968
        have b2e122798 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e122751
             have i₂ := b2e77650 y
             grind)
          | exact superpose b2e77650 b2e122751
          | exact resolve b2e122751 b2e77650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77650 b2e122751
        have b2e127877 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b2e13 (M.op y y)
             have i₂ := b2e122798
             grind)
          | exact superpose b2e122798 b2e13
          | exact resolve b2e13 b2e122798
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122798
        have b2e127997 : y = (M.op y y) := by
          first
          | (have i₁ := b2e127877
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e127877
          | exact resolve b2e127877 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e127877
        have b2e128578 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27 y X0 y
             have i₂ := b2e127997
             grind)
          | exact superpose b2e127997 b2e27
          | exact resolve b2e27 b2e127997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e128682 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e128578 X0
             have i₂ := b2e127997
             grind)
          | exact superpose b2e127997 b2e128578
          | exact resolve b2e128578 b2e127997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e128578
        have b2e128738 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e128682 X0
             have i₂ := b2e127997
             grind)
          | exact superpose b2e127997 b2e128682
          | exact resolve b2e128682 b2e127997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e127997 b2e128682
        have b2e129829 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e14077
             have i₂ := b2e128738 x
             grind)
          | exact superpose b2e128738 b2e14077
          | exact resolve b2e14077 b2e128738
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14077 b2e128738
        have b2e129852 : False := by grind
        exact b2e129852
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : y ≠ y ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 y x
             grind)
          | (have r₁ := b3e15 y x
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : (M.op y x) = (k y x) := by grind
        clear b3e34
        have b3e42 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | (have r₁ := b3e16 (σ y) (σ x)
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b3e42
        have b3e47 : (σ x) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b3e45
             have r₂ := b3e23
             grind)
          | exact resolve b3e45 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e45
        have b3e49 : (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b3e47
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e47
          | exact resolve b3e47 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e50 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e49
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e49
          | exact resolve b3e49 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e49
        have b3e59 : (M.op y x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (M.op y x)
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e13
          | exact resolve b3e13 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e60 : x = (M.op y x) := by
          first
          | (have i₁ := b3e59
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e59
          | exact resolve b3e59 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e63 : False := by grind
        exact b3e63
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ y) ≠ (σ y) := by
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e30 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b5e13 X0 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : y ≠ y ∨ (M.op y x) = (k y x) := by
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
          have b5e38 : (M.op y x) = (k y x) := by grind
          clear b5e35
          have b5e39 : y ≠ y ∨ x = (M.op y x) ∨ y = (k x y) := by
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
          have b5e42 : x = (M.op y x) ∨ y = (k x y) := by grind
          clear b5e39
          have b5e43 : y = (k x y) := by
            first
            | (have r₁ := b5e42
               have r₂ := b5e21
               grind)
            | exact resolve b5e42 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e59 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e83 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e59 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e59
            | exact resolve b5e59 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e225 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) (M.op (σ X0) (σ (k X0 X1))))) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e30 (σ X1) X2 (σ X0)
               have i₂ := b5e47 X1 X0
               grind)
            | exact superpose b5e47 b5e30
            | (have j1 := b5e47 X1 X0
               grind)
            | exact resolve b5e30 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e227 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 (σ X0) (σ X1)
               have i₂ := b5e47 X1 X0
               grind)
            | exact superpose b5e47 b5e16
            | (have j0 := b5e16 (σ X0) (σ X1)
               have j1 := b5e47 X1 X0
               grind)
            | (have r₁ := b5e16 (σ X0) (σ X1)
               have r₂ := b5e47 X0 X1
               grind)
            | (have r₁ := b5e16 (σ X1) (σ X0)
               have r₂ := b5e47 X0 X1
               grind)
            | exact resolve b5e16 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e229 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e47 x y
               grind)
            | exact superpose b5e47 b5e23
            | (have j1 := b5e47 x y
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e47 x y
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e47 y x
               grind)
            | exact resolve b5e23 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e242 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e229
          have b5e247 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e242
               have r₂ := b5e24
               grind)
            | exact resolve b5e242 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e242
          have b5e248 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e227 X0 X1
               have j1 := b5e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b5e227 X0 X1
               have r₂ := b5e16 (σ X1) (σ X0)
               grind)
            | (have r₁ := b5e227 X0 X1
               have r₂ := b5e16 (σ X0) (σ X1)
               grind)
            | exact resolve b5e227 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e227
          have b5e253 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e247
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e247
            | exact resolve b5e247 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e247
          have b5e254 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e248 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e248
            | (have j0 := b5e248 X0 X1
               grind)
            | exact resolve b5e248 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248
          have b5e255 : (σ y) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e253
               grind)
            | exact superpose b5e253 b5e24
            | exact resolve b5e24 b5e253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e258 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ (M.op y x))))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e30 (σ x) X0 (σ y)
               have i₂ := b5e253
               grind)
            | exact superpose b5e253 b5e30
            | exact resolve b5e30 b5e253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e14812 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e254 (τ X1) (τ X0)
               have i₂ := b5e83 X0 X1
               grind)
            | exact superpose b5e83 b5e254
            | (have j0 := b5e254 (τ X0) (τ X1)
               grind)
            | exact resolve b5e254 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e254
          have b5e14843 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14812 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e14812
            | (have j0 := b5e14812 X0 X1
               grind)
            | exact resolve b5e14812 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14812
          have b5e14853 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14843 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e14843
            | (have j0 := b5e14843 X0 X1
               grind)
            | exact resolve b5e14843 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14843
          have b5e14862 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14853 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e14853
            | (have j0 := b5e14853 X0 X1
               grind)
            | exact resolve b5e14853 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14853
          have b5e14870 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14862 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e14862
            | (have j0 := b5e14862 X0 X1
               grind)
            | exact resolve b5e14862 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14862
          have b5e14876 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14870 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e14870
            | (have j0 := b5e14870 X0 X1
               grind)
            | exact resolve b5e14870 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14870
          have b5e14879 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e14876 X0 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e14876
            | (have j0 := b5e14876 X0 X1
               grind)
            | exact resolve b5e14876 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14876
          have b5e14880 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e14879 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e14879
            | (have j0 := b5e14879 X0 X1
               grind)
            | exact resolve b5e14879 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14879
          have b5e15409 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e225 x y X0
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e225
            | (have j0 := b5e225 x y x
               grind)
            | exact resolve b5e225 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e225
          have b5e15649 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) := by
            intro X0
            first
            | (have j0 := b5e15409 X0
               grind)
            | (have r₁ := b5e15409 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e15409 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15409
          have b5e15664 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 := by
            intro X0
            first
            | (have j0 := b5e15649 X0
               grind)
            | (have r₁ := b5e15649 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e15649 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15649
          have b5e15677 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ (M.op y x)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e15664 X0
               have i₂ := b5e253
               grind)
            | exact superpose b5e253 b5e15664
            | exact resolve b5e15664 b5e253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e253 b5e15664
          have b5e15888 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e258 X0
               have i₂ := b5e15677 (σ x)
               grind)
            | exact superpose b5e15677 b5e258
            | exact resolve b5e258 b5e15677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e258 b5e15677
          have b5e16338 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e16 (σ x) X0
               have i₂ := b5e15888 X0
               grind)
            | exact superpose b5e15888 b5e16
            | (have j0 := b5e16 (σ x) X0
               grind)
            | (have r₁ := b5e16 (σ x) (σ x)
               have r₂ := b5e15888 (σ x)
               grind)
            | exact resolve b5e16 b5e15888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e22353 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
            first
            | (have j0 := b5e16338 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16338
          have b5e22354 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
            first
            | (have i₁ := b5e22353
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e22353
            | exact resolve b5e22353 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22353
          have b5e22355 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b5e22354
               have i₂ := b5e15888 (σ x)
               grind)
            | exact superpose b5e15888 b5e22354
            | exact resolve b5e22354 b5e15888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15888 b5e22354
          have b5e22593 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 (k x x)
               have i₂ := b5e22355
               grind)
            | exact superpose b5e22355 b5e14
            | exact resolve b5e14 b5e22355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22355
          have b5e22689 : x = (k x x) := by
            first
            | (have i₁ := b5e22593
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e22593
            | exact resolve b5e22593 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22593
          have b5e23223 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e14880 x x
               have i₂ := b5e22689
               grind)
            | exact superpose b5e22689 b5e14880
            | (have j0 := b5e14880 x x
               grind)
            | (have r₁ := b5e14880 x x
               have r₂ := b5e22689
               grind)
            | exact resolve b5e14880 b5e22689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14880 b5e22689
          have b5e23224 : x ≠ x ∨ x = (M.op x x) := by grind
          clear b5e23223
          have b5e23225 : x = (M.op x x) := by grind
          clear b5e23224
          have b5e23685 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e30 x X0 x
               have i₂ := b5e23225
               grind)
            | exact superpose b5e23225 b5e30
            | exact resolve b5e30 b5e23225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e23739 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23685 X0
               have i₂ := b5e23225
               grind)
            | exact superpose b5e23225 b5e23685
            | exact resolve b5e23685 b5e23225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23685
          have b5e23768 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23739 X0
               have i₂ := b5e23225
               grind)
            | exact superpose b5e23225 b5e23739
            | exact resolve b5e23739 b5e23225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23225 b5e23739
          have b5e24427 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e255
               have i₂ := b5e23768 y
               grind)
            | exact superpose b5e23768 b5e255
            | exact resolve b5e255 b5e23768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e255 b5e23768
          have b5e24436 : False := by grind
          exact b5e24436
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X0 (M.op X2 (M.op X0 X2))
             have i₂ := b6e12 X0 X2 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e35 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e33
        have b6e36 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e35
          | exact resolve b6e35 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e45 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
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
        have b6e47 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b6e45
        have b6e48 : (σ y) = (σ (k x y)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e47
             have i₂ := b6e36
             grind)
          | exact superpose b6e36 b6e47
          | exact resolve b6e47 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e49 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e48
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e48
          | exact resolve b6e48 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e52 : (σ y) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e36
             grind)
          | exact superpose b6e36 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | exact resolve b6e15 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e54 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e52
          | exact resolve b6e52 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e55 : (σ x) = (σ (k y x)) ∨ (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e54
          | exact resolve b6e54 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e56 : (σ x) = (σ (k y x)) := by
          first
          | (have r₁ := b6e55
             have r₂ := b6e49
             grind)
          | exact resolve b6e55 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e55
        have b6e58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e61 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e56
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e56
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e56 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e64 : (k y x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e13
          | exact resolve b6e13 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e65 : x = (k y x) := by
          first
          | (have i₁ := b6e64
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e64
          | exact resolve b6e64 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e68 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e61
             have r₂ := b6e20
             grind)
          | exact resolve b6e61 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e69 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e68
             have r₂ := b6e21
             grind)
          | exact resolve b6e68 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e82 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e17
          | (have j0 := b6e17 y x
             grind)
          | exact resolve b6e17 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e83 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e82
             have r₂ := b6e20
             grind)
          | exact resolve b6e82 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e85 : x = (M.op x y) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e21
             grind)
          | exact resolve b6e83 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e95 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e27 x X0 y
             have i₂ := b6e85
             grind)
          | exact superpose b6e85 b6e27
          | exact resolve b6e27 b6e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e241 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e58 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e243 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e241 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e241
        have b6e293 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e27 y X0 x
             have i₂ := b6e95 y
             grind)
          | exact superpose b6e95 b6e27
          | exact resolve b6e27 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e341 : ∀ X0 : G, y ≠ X0 ∨ (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e15 y X0
             have i₂ := b6e293 X0
             grind)
          | exact superpose b6e293 b6e15
          | (have j0 := b6e15 y X0
             grind)
          | (have r₁ := b6e15 y y
             have r₂ := b6e293 y
             grind)
          | exact resolve b6e15 b6e293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e644 : (M.op y y) = (k y y) := by
          first
          | (have j0 := b6e341 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e341
        have b6e645 : y = (k y y) := by
          first
          | (have i₁ := b6e644
             have i₂ := b6e293 y
             grind)
          | exact superpose b6e293 b6e644
          | exact resolve b6e644 b6e293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e293 b6e644
        have b6e1454 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e243 y
             have i₂ := b6e645
             grind)
          | exact superpose b6e645 b6e243
          | (have j0 := b6e243 y
             grind)
          | exact resolve b6e243 b6e645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e243 b6e645
        have b6e1457 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e1454
        have b6e1470 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e27 (σ y) X0 (σ y)
             have i₂ := b6e1457
             grind)
          | exact superpose b6e1457 b6e27
          | exact resolve b6e27 b6e1457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e1483 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1470 X0
             have i₂ := b6e1457
             grind)
          | exact superpose b6e1457 b6e1470
          | exact resolve b6e1470 b6e1457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1470
        have b6e1493 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1483 X0
             have i₂ := b6e1457
             grind)
          | exact superpose b6e1457 b6e1483
          | exact resolve b6e1483 b6e1457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1457 b6e1483
        have b6e1691 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e1493 (σ x)
             grind)
          | exact superpose b6e1493 b6e19
          | exact resolve b6e19 b6e1493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1493
        have b6e1698 : False := by grind
        exact b6e1698
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b7e13 X0 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
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
          have b7e46 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
          clear b7e44
          have b7e47 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e52 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e55 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e52
          have b7e56 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e55
               have r₂ := b7e23
               grind)
            | exact resolve b7e55 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e57 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e56
            | exact resolve b7e56 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e14
            | exact resolve b7e14 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e61 : y = (k x y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e60
            | exact resolve b7e60 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e72 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e61
               grind)
            | exact superpose b7e61 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e73 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e22
               grind)
            | exact resolve b7e72 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e75 : y = (M.op y x) := by
            first
            | (have r₁ := b7e73
               have r₂ := b7e21
               grind)
            | exact resolve b7e73 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e89 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 y X0 x
               have i₂ := b7e75
               grind)
            | exact superpose b7e75 b7e34
            | exact resolve b7e34 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e235 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e66 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e237 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e235 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e235
          have b7e283 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 x X0 y
               have i₂ := b7e89 x
               grind)
            | exact superpose b7e89 b7e34
            | exact resolve b7e34 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e331 : ∀ X0 : G, x ≠ X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b7e16 x X0
               have i₂ := b7e283 X0
               grind)
            | exact superpose b7e283 b7e16
            | (have j0 := b7e16 x X0
               grind)
            | (have r₁ := b7e16 x x
               have r₂ := b7e283 x
               grind)
            | exact resolve b7e16 b7e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e630 : (M.op x x) = (k x x) := by
            first
            | (have j0 := b7e331 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e331
          have b7e631 : x = (k x x) := by
            first
            | (have i₁ := b7e630
               have i₂ := b7e283 x
               grind)
            | exact superpose b7e283 b7e630
            | exact resolve b7e630 b7e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e283 b7e630
          have b7e1424 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e237 x
               have i₂ := b7e631
               grind)
            | exact superpose b7e631 b7e237
            | (have j0 := b7e237 x
               grind)
            | exact resolve b7e237 b7e631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e237 b7e631
          have b7e1427 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e1424
          have b7e1440 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 (σ x) X0 (σ x)
               have i₂ := b7e1427
               grind)
            | exact superpose b7e1427 b7e34
            | exact resolve b7e34 b7e1427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e1453 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1440 X0
               have i₂ := b7e1427
               grind)
            | exact superpose b7e1427 b7e1440
            | exact resolve b7e1440 b7e1427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1440
          have b7e1463 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1453 X0
               have i₂ := b7e1427
               grind)
            | exact superpose b7e1427 b7e1453
            | exact resolve b7e1453 b7e1427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1427 b7e1453
          have b7e1660 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e1463 (σ y)
               grind)
            | exact superpose b7e1463 b7e47
            | exact resolve b7e47 b7e1463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47 b7e1463
          have b7e1998 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e1660
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e1660
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e1660 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1660
          have b7e2032 : x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e1998
               have r₂ := b7e25
               grind)
            | exact resolve b7e1998 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e1998
          have b7e2033 : y = (M.op x y) := by
            first
            | (have r₁ := b7e2032
               have r₂ := b7e21
               grind)
            | exact resolve b7e2032 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2032
          have b7e2034 : False := by grind
          exact b7e2034
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e192 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e65 x y
               grind)
            | exact superpose b8e65 b8e23
            | (have j1 := b8e65 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e65 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e65 y x
               grind)
            | exact resolve b8e23 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e205 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e192
          have b8e210 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e205
               have r₂ := b8e24
               grind)
            | exact resolve b8e205 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e205
          have b8e217 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e210
               grind)
            | exact superpose b8e210 b8e20
            | exact resolve b8e20 b8e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210
          have b8e282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e217
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e217
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e217 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e217
          have b8e283 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e282
          have b8e284 : y = (M.op x y) := by
            first
            | (have r₁ := b8e283
               have r₂ := b8e21
               grind)
            | exact resolve b8e283 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e283
          have b8e285 : False := by grind
          exact b8e285

/-- `Equation1101`: `x = y ◇ ((x ◇ (z ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_y_pxx_pyx_pxy_Equation1101 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1101 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1101.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X2)) X1)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
           have i₂ := b0e11 X0 (M.op X0 (M.op X2 X2)) X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e39 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e41 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e39
      have b0e42 : (M.op x x) = (k x y) := by grind
      clear b0e38
      have b0e43 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e41
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e41
        | exact resolve b0e41 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e44 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e43
        | exact resolve b0e43 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e43
      have b0e111 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X2)) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 x
           have i₂ := b0e24 X1 X0 x
           grind)
        | (have i₁ := b0e11 X1 X1 X1
           have i₂ := b0e24 X1 X1 X2
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e4566 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x (M.op x x)) X0)) := by
        intro X0
        first
        | (have i₁ := b0e111 x y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e111
        | exact resolve b0e111 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111
      have b0e4691 : x = y := by
        first
        | (have i₁ := b0e4566 x
           have i₂ := b0e11 x x x
           grind)
        | exact superpose b0e11 b0e4566
        | exact resolve b0e4566 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4566
      have b0e4716 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e4691
           grind)
        | exact superpose b0e4691 b0e18
        | exact resolve b0e18 b0e4691
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4691
      have b0e4717 : False := by grind
      exact b0e4717
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x x) = (M.op y x) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : (σ y) = (k (σ x) (σ x)) := by grind
        clear b1e36
        have b1e39 : (M.op x x) = (k x y) := by grind
        clear b1e35
        have b1e40 : (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e38
          | exact resolve b1e38 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e41 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e37 x
             grind)
          | exact superpose b1e37 b1e40
          | exact resolve b1e40 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e40
        have b1e76 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e80 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e76
             have r₂ := b1e24
             grind)
          | exact resolve b1e76 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e81 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e80
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e80
          | exact resolve b1e80 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e82 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e81
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e81
          | exact resolve b1e81 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e81
        have b1e83 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e82
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e82
          | exact resolve b1e82 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e82
        have b1e84 : False := by grind
        exact b1e84
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X2)) X1)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e30 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
             have i₂ := b2e12 X0 (M.op X0 (M.op X2 X2)) X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : (M.op x x) = (k x y) := by grind
        clear b2e48
        have b2e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e49 (σ X0)
             grind)
          | exact superpose b2e49 b2e18
          | exact resolve b2e18 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e52 X0
             have i₂ := b2e49 X0
             grind)
          | exact superpose b2e49 b2e52
          | exact resolve b2e52 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e87 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e67 X0 X1
             have i₂ := b2e59 X0
             grind)
          | exact superpose b2e59 b2e67
          | (have j0 := b2e67 X0 X1
             grind)
          | exact resolve b2e67 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e87 X0 X1
             have i₂ := b2e59 X0
             grind)
          | exact superpose b2e59 b2e87
          | (have j0 := b2e87 X0 X1
             grind)
          | exact resolve b2e87 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59 b2e87
        have b2e134 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2 x
             have i₂ := b2e30 X1 X0 x
             grind)
          | (have i₁ := b2e12 X1 X1 X1
             have i₂ := b2e30 X1 X1 X2
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e142 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 (M.op X3 X3) X2
             have i₂ := b2e30 (M.op X1 (M.op X2 X2)) X0 X3
             grind)
          | (have i₁ := b2e12 X0 (M.op X0 (M.op X0 (M.op X2 X2))) X2
             have i₂ := b2e30 X0 (M.op X0 (M.op X2 X2)) X2
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e146 : ∀ X1 X3 : G, (M.op (M.op X3 X3) X1) = X1 := by
          intro X1 X3
          first
          | (have i₁ := b2e142 x X1 x X3
             have i₂ := b2e12 X1 x x
             grind)
          | exact superpose b2e12 b2e142
          | exact resolve b2e142 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e142
        have b2e155 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op X1 X1) X0 X1
             have i₂ := b2e146 X0 (M.op X1 X1)
             grind)
          | exact superpose b2e146 b2e12
          | exact resolve b2e12 b2e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e146
        have b2e275 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e155 X0 X1
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e155 X0 X1
             grind)
          | exact superpose b2e155 b2e15
          | (have j0 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e155 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e155 X0 X0
             grind)
          | exact resolve b2e15 b2e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e155
        have b2e280 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e275 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e275
        have b2e432 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X1
             have i₂ := b2e280 X0 (σ X1)
             grind)
          | exact superpose b2e280 b2e18
          | exact resolve b2e18 b2e280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e280
        have b2e440 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e432 X0 X1
             have i₂ := b2e49 X1
             grind)
          | exact superpose b2e49 b2e432
          | exact resolve b2e432 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e432
        have b2e983 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e440 (σ x) X0
             grind)
          | exact superpose b2e440 b2e22
          | exact resolve b2e22 b2e440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1100 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e89 x y
             grind)
          | exact superpose b2e89 b2e21
          | (have j1 := b2e89 x y
             grind)
          | exact resolve b2e21 b2e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e1114 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
          first
          | (have r₁ := b2e1100
             have r₂ := b2e440 (σ x) x
             grind)
          | exact resolve b2e1100 b2e440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e440 b2e1100
        have b2e1142 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e1114
             have r₂ := b2e983 x
             grind)
          | exact resolve b2e1114 b2e983
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e983 b2e1114
        have b2e1163 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1142
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e1142
          | exact resolve b2e1142 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e1142
        have b2e2699 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e1163
             grind)
          | exact superpose b2e1163 b2e19
          | exact resolve b2e19 b2e1163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1163
        have b2e3642 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x (M.op x x)) X0)) := by
          intro X0
          first
          | (have i₁ := b2e134 x y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e134
          | exact resolve b2e134 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134
        have b2e3744 : x = y := by
          first
          | (have i₁ := b2e3642 x
             have i₂ := b2e12 x x x
             grind)
          | exact superpose b2e12 b2e3642
          | exact resolve b2e3642 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3642
        have b2e3766 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e2699
             have i₂ := b2e3744
             grind)
          | exact superpose b2e3744 b2e2699
          | exact resolve b2e2699 b2e3744
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2699 b2e3744
        have b2e3767 : False := by grind
        exact b2e3767
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X2)) X1)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : y ≠ (M.op y x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op X0 y) X1 (M.op X0 y)
             have i₂ := b3e31 (M.op X0 y) X0
             grind)
          | exact superpose b3e31 b3e12
          | exact resolve b3e12 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e31 x X0
             have i₂ := b3e36 (M.op X0 y) x
             grind)
          | exact superpose b3e36 b3e31
          | exact resolve b3e31 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e52
        have b3e56 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e54
          | exact resolve b3e54 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e102 : ∀ X0 : G, (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e36 (M.op X0 y) y
             have i₂ := b3e46 X0
             grind)
          | exact superpose b3e46 b3e36
          | exact resolve b3e36 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e46
        have b3e106 : (M.op y x) = (k x y) ∨ y = (M.op y x) := by grind
        have b3e109 : (M.op y x) = (k x y) := by
          first
          | (have r₁ := b3e106
             have r₂ := b3e24
             grind)
          | exact resolve b3e106 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e110 : x = (k x y) := by
          first
          | (have i₁ := b3e109
             have i₂ := b3e102 x
             grind)
          | exact superpose b3e102 b3e109
          | exact resolve b3e109 b3e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e109
        have b3e137 : x ≠ y := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e102 x
             grind)
          | exact superpose b3e102 b3e24
          | exact resolve b3e24 b3e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e102
        have b3e152 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e15
          | exact resolve b3e15 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e154 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e152
        have b3e156 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e154
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e154
          | exact resolve b3e154 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e154
        have b3e163 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e156
             have i₂ := b3e53 x
             grind)
          | exact superpose b3e53 b3e156
          | exact resolve b3e156 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e156
        have b3e170 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e163
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e163
          | exact resolve b3e163 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e163
        have b3e173 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e170
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e170
          | exact resolve b3e170 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e110 b3e170
        have b3e177 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e173
             grind)
          | exact superpose b3e173 b3e13
          | exact resolve b3e13 b3e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e173
        have b3e178 : x = y := by
          first
          | (have i₁ := b3e177
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e177
          | exact resolve b3e177 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e177
        have b3e182 : False := by grind
        exact b3e182
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X2)) X1)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : y ≠ (M.op y x) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b4e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e34 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X3 X3))) X0) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 (M.op X3 X3))) X3
               have i₂ := b4e13 X0 (M.op X2 (M.op X3 X3)) X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) (M.op X1 y)) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (M.op (M.op X0 y) (M.op X1 y)) X1
               have i₂ := b4e34 (M.op X1 y) X0
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 y) X1 (M.op X0 y)
               have i₂ := b4e34 (M.op X0 y) X0
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e46 (σ X0)
               grind)
            | exact superpose b4e46 b4e19
            | exact resolve b4e19 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e53 X0
               have i₂ := b4e46 X0
               grind)
            | exact superpose b4e46 b4e53
            | exact resolve b4e53 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b4e65 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 (M.op X0 X1)) X2)) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 X2 X1
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X0
               have i₂ := b4e18 X0 X0
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e68 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X1 (M.op X2 X2)))) = X1 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = (k (M.op X1 (M.op X2 X2)) X0) ∨ (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X1 (M.op X2 X2)) X2
               have i₂ := b4e18 (M.op X1 (M.op X2 X2)) X0
               grind)
            | (have i₁ := b4e13 X0 X0 X2
               have i₂ := b4e18 X0 (M.op X0 (M.op X2 X2))
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 (M.op X1 (M.op X2 X2)) X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 (M.op X1 X0)
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e83 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (k (M.op X1 (M.op X2 X2)) X0) ∨ (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))) = X0 ∨ (M.op X0 y) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e68 X0 X1 X2
               have i₂ := b4e40 X0 (M.op X1 (M.op X2 X2))
               grind)
            | exact superpose b4e40 b4e68
            | (have j0 := b4e68 X0 X1 X2
               grind)
            | exact resolve b4e68 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e86 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op X0 X1)) y) = X3 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e65 X0 X1 x X3
               have i₂ := b4e40 (M.op X3 (M.op X0 X1)) x
               grind)
            | exact superpose b4e40 b4e65
            | (have j0 := b4e65 X0 X1 x X3
               grind)
            | exact resolve b4e65 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65
          have b4e87 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e62 X0 X1
               have i₂ := b4e56 X0
               grind)
            | exact superpose b4e56 b4e62
            | (have j0 := b4e62 X0 X1
               grind)
            | exact resolve b4e62 b4e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e87 X0 X1
               have i₂ := b4e56 X0
               grind)
            | exact superpose b4e56 b4e87
            | (have j0 := b4e87 X0 X1
               grind)
            | exact resolve b4e87 b4e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56 b4e87
          have b4e91 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e40 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e40
            | exact resolve b4e40 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e93 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op (M.op X0 y) X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X1 (M.op (M.op X0 y) X1)
               have i₂ := b4e34 X1 X0
               grind)
            | exact superpose b4e34 b4e40
            | exact resolve b4e40 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e94 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X1 (M.op X0 X1)
               have i₂ := b4e40 X0 X1
               grind)
            | exact superpose b4e40 b4e40
            | exact resolve b4e40 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) y) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x X1
               have i₂ := b4e40 (M.op X0 (M.op X1 X1)) x
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e101 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 x X0
               have i₂ := b4e40 (M.op X0 y) x
               grind)
            | exact superpose b4e40 b4e34
            | exact resolve b4e34 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e102 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) (M.op X0 y)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (M.op X0 (M.op X1 y)) X1
               have i₂ := b4e40 X0 (M.op X1 y)
               grind)
            | exact superpose b4e40 b4e34
            | exact resolve b4e34 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e106 : (M.op y x) = (k x y) ∨ y = (M.op y x) := by grind
          have b4e107 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          have b4e111 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e107
               have r₂ := b4e26
               grind)
            | exact resolve b4e107 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e107
          have b4e112 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b4e106
               have r₂ := b4e27
               grind)
            | exact resolve b4e106 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e106
          have b4e113 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e111
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e111
            | exact resolve b4e111 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111
          have b4e114 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e113
               have i₂ := b4e112
               grind)
            | exact superpose b4e112 b4e113
            | exact resolve b4e113 b4e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112 b4e113
          have b4e124 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e29 X1 X0
               grind)
            | exact superpose b4e29 b4e14
            | exact resolve b4e14 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e131 : ∀ X0 : G, (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e40 (M.op X0 y) y
               have i₂ := b4e101 X0
               grind)
            | exact superpose b4e101 b4e40
            | exact resolve b4e40 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e142 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 (σ y)) X1 (M.op X0 (σ y))
               have i₂ := b4e35 (M.op X0 (σ y)) X0
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e145 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op (M.op X0 (σ y)) X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X1 (M.op (M.op X0 (σ y)) X1)
               have i₂ := b4e35 X1 X0
               grind)
            | exact superpose b4e35 b4e40
            | exact resolve b4e40 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e148 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e142 X0 x
               have i₂ := b4e40 X0 x
               grind)
            | exact superpose b4e40 b4e142
            | exact resolve b4e142 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142
          have b4e172 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e131 y
               grind)
            | exact superpose b4e131 b4e16
            | exact resolve b4e16 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e174 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e40 y X0
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e40
            | exact resolve b4e40 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e182 : x ≠ y := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e131 x
               grind)
            | exact superpose b4e131 b4e27
            | exact resolve b4e27 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e188 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b4e174 X0
               have i₂ := b4e131 y
               grind)
            | exact superpose b4e131 b4e174
            | exact resolve b4e174 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e174
          have b4e193 : (σ y) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e114
               grind)
            | exact superpose b4e114 b4e26
            | exact resolve b4e26 b4e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e198 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b4e193
               have i₂ := b4e131 x
               grind)
            | exact superpose b4e131 b4e193
            | exact resolve b4e193 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193
          have b4e353 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ y = (M.op y X0) := by
            intro X0
            grind
          have b4e355 : ∀ X0 X1 : G, (M.op X1 X0) ≠ y ∨ (k X0 X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e188 X0
               grind)
            | exact superpose b4e188 b4e16
            | exact resolve b4e16 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e360 : ∀ X0 : G, y ≠ y ∨ y = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e188 X0
               grind)
            | exact superpose b4e188 b4e16
            | exact resolve b4e16 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e364 : y = (σ y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e188 (σ x)
               grind)
            | exact superpose b4e188 b4e24
            | exact resolve b4e24 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e370 : ∀ X0 : G, y = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e360 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e360
          have b4e376 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e353 X0
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e353
            | (have j0 := b4e353 X0
               grind)
            | exact resolve b4e353 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e353
          have b4e381 : ∀ X0 : G, (k X0 y) = X0 ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e376 X0
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e376
            | (have j0 := b4e376 X0
               grind)
            | exact resolve b4e376 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e376
          have b4e402 : y ≠ (σ x) := by
            first
            | (have i₁ := b4e198
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e198
            | exact resolve b4e198 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e405 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e20
            | exact resolve b4e20 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e407 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 y
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e19
            | exact resolve b4e19 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e408 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e19
            | exact resolve b4e19 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e409 : y = (τ y) := by
            first
            | (have i₁ := b4e14 y
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e14
            | exact resolve b4e14 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e414 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X0 X1)) (M.op X3 (M.op X4 X4))) X2) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e37 X2 X1 X3 X4
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e37 X0 X0 X2 X3
               have i₂ := b4e18 X0 X0
               grind)
            | exact superpose b4e18 b4e37
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e37 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e458 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X3 X3))) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e40 (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X3 X3))) X1
               have i₂ := b4e37 X1 X2 X0 X3
               grind)
            | exact superpose b4e37 b4e40
            | exact resolve b4e40 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e477 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X0 y)) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e458 X0 X1 X2 x
               have i₂ := b4e188 x
               grind)
            | exact superpose b4e188 b4e458
            | exact resolve b4e458 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e458
          have b4e507 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X0 X1)) (M.op X3 y)) X2) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e414 X0 X1 X2 X3 x
               have i₂ := b4e188 x
               grind)
            | exact superpose b4e188 b4e414
            | (have j0 := b4e414 X0 X1 X2 X3 x
               grind)
            | exact resolve b4e414 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e414
          have b4e517 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 y) (M.op X0 y)) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e477 X0 X1 x
               have i₂ := b4e188 x
               grind)
            | exact superpose b4e188 b4e477
            | exact resolve b4e477 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e477
          have b4e534 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X0 X1)) (M.op X3 y)) X2) = X3 ∨ y = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e507 X0 X1 X2 X3
               have i₂ := b4e188 X1
               grind)
            | exact superpose b4e188 b4e507
            | (have j0 := b4e507 X0 X1 X2 X3
               grind)
            | exact resolve b4e507 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e507
          have b4e657 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76
          have b4e660 : ∀ X0 X1 : G, (M.op X0 X1) ≠ y ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e657 X0 X1
               have i₂ := b4e188 X0
               grind)
            | exact superpose b4e188 b4e657
            | (have j0 := b4e657 X0 X1
               grind)
            | exact resolve b4e657 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e657
          have b4e697 : ∀ X0 X1 : G, (M.op X0 X1) ≠ y ∨ y = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e660 X0 X1
               have i₂ := b4e188 X0
               grind)
            | exact superpose b4e188 b4e660
            | (have j0 := b4e660 X0 X1
               grind)
            | (have r₁ := b4e660 X0 X0
               have r₂ := b4e188 X0
               grind)
            | exact resolve b4e660 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e660
          have b4e863 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X0)) = X1 ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = X1 ∨ (k (M.op X2 X2) X1) = (M.op (M.op X2 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e37 y X0 X1 X2
               have i₂ := b4e86 X1 (M.op X2 X2) (M.op y (M.op X0 X0))
               grind)
            | exact superpose b4e86 b4e37
            | (have j1 := b4e86 X1 (M.op X2 X2) x
               grind)
            | exact resolve b4e37 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e86
          have b4e906 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = X1 ∨ (k (M.op X2 X2) X1) = (M.op (M.op X2 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e863 X0 X1 X2
               have i₂ := b4e131 (M.op X0 X0)
               grind)
            | exact superpose b4e131 b4e863
            | (have j0 := b4e863 X0 X1 X2
               grind)
            | exact resolve b4e863 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e863
          have b4e945 : ∀ X1 X2 : G, y = X1 ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = X1 ∨ (k (M.op X2 X2) X1) = (M.op (M.op X2 X2) X1) := by
            intro X1 X2
            first
            | (have i₁ := b4e906 x X1 X2
               have i₂ := b4e188 x
               grind)
            | exact superpose b4e188 b4e906
            | (have j0 := b4e906 (M.op X2 X2) X1 X2
               grind)
            | exact resolve b4e906 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e906
          have b4e972 : ∀ X1 X2 : G, y = X1 ∨ y = X1 ∨ (k (M.op X2 X2) X1) = (M.op (M.op X2 X2) X1) := by
            intro X1 X2
            first
            | (have i₁ := b4e945 X1 X2
               have i₂ := b4e188 (M.op X2 X2)
               grind)
            | exact superpose b4e188 b4e945
            | (have j0 := b4e945 X1 X2
               grind)
            | exact resolve b4e945 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e945
          have b4e973 : ∀ X1 X2 : G, y = X1 ∨ (k (M.op X2 X2) X1) = (M.op (M.op X2 X2) X1) := by
            intro X1 X2
            first
            | (have j0 := b4e972 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e972
          have b4e987 : ∀ X1 : G, (k y X1) = (M.op y X1) ∨ y = X1 := by
            intro X1
            first
            | (have i₁ := b4e973 X1 x
               have i₂ := b4e188 x
               grind)
            | exact superpose b4e188 b4e973
            | (have j0 := b4e973 X1 x
               grind)
            | exact resolve b4e973 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e973
          have b4e993 : ∀ X1 : G, (k y X1) = X1 ∨ y = X1 := by
            intro X1
            first
            | (have i₁ := b4e987 X1
               have i₂ := b4e131 X1
               grind)
            | exact superpose b4e131 b4e987
            | (have j0 := b4e987 X1
               grind)
            | exact resolve b4e987 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e987
          have b4e1584 : (σ (M.op y x)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e114
               have i₂ := b4e89 y x
               grind)
            | exact superpose b4e89 b4e114
            | (have j1 := b4e89 y x
               grind)
            | exact resolve b4e114 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89 b4e114
          have b4e1655 : (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e1584
               have i₂ := b4e131 x
               grind)
            | exact superpose b4e131 b4e1584
            | exact resolve b4e1584 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1584
          have b4e1730 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e1655
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e1655
            | exact resolve b4e1655 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1655
          have b4e1795 : (σ y) = (M.op (σ x) y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e1730
               have i₂ := b4e91
               grind)
            | exact superpose b4e91 b4e1730
            | exact resolve b4e1730 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e1730
          have b4e1853 : y = (M.op (σ x) y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e1795
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e1795
            | exact resolve b4e1795 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1795
          have b4e1906 : (σ x) = (σ y) ∨ y = (M.op (σ x) y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b4e1853
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e1853
            | exact resolve b4e1853 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1853
          have b4e1945 : (σ x) = (σ (k y x)) ∨ y = (M.op (σ x) y) := by
            first
            | (have r₁ := b4e1906
               have r₂ := b4e198
               grind)
            | exact resolve b4e1906 b4e198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e198 b4e1906
          have b4e2614 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e28 X0 y
               have i₂ := b4e381 (τ X0)
               grind)
            | exact superpose b4e381 b4e28
            | (have j1 := b4e381 (τ X0)
               grind)
            | exact resolve b4e28 b4e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2616 : ∀ X0 : G, (σ (τ X0)) = (k X0 y) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e2614 X0
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e2614
            | (have j0 := b4e2614 X0
               grind)
            | exact resolve b4e2614 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2614
          have b4e2617 : ∀ X0 : G, (k X0 y) = X0 ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e2616 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e2616
            | (have j0 := b4e2616 X0
               grind)
            | exact resolve b4e2616 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2616
          have b4e3969 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) = (k (M.op (M.op X1 X1) (M.op X1 X1)) X0) ∨ (M.op X1 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e100 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)
               have i₂ := b4e83 X0 (M.op X1 X1) X1
               grind)
            | (have i₁ := b4e100 X0 X1
               have i₂ := b4e83 (M.op X0 (M.op X1 X1)) X1 x
               grind)
            | exact superpose b4e83 b4e100
            | (have j1 := b4e83 X0 (M.op X1 X1) X1
               grind)
            | exact resolve b4e100 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83 b4e100
          have b4e4033 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) = (k (M.op (M.op X1 X1) (M.op X1 X1)) X0) ∨ (M.op X1 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e3969 X0 X1
               have i₂ := b4e188 (M.op X1 X1)
               grind)
            | exact superpose b4e188 b4e3969
            | (have j0 := b4e3969 X0 X1
               grind)
            | exact resolve b4e3969 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3969
          have b4e4131 : ∀ X0 X1 : G, (k y X0) = (M.op y X0) ∨ y = (M.op X0 y) ∨ (M.op X1 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e4033 X0 X1
               have i₂ := b4e188 (M.op X1 X1)
               grind)
            | exact superpose b4e188 b4e4033
            | (have j0 := b4e4033 X0 X1
               grind)
            | exact resolve b4e4033 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4033
          have b4e4214 : ∀ X0 X1 : G, (k y X0) = X0 ∨ y = (M.op X0 y) ∨ (M.op X1 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e4131 X0 X1
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e4131
            | (have j0 := b4e4131 X0 X1
               grind)
            | exact resolve b4e4131 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4131
          have b4e4266 : ∀ X0 : G, y = (M.op X0 y) ∨ (k y X0) = X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e4214 X0 x
               have i₂ := b4e188 x
               grind)
            | exact superpose b4e188 b4e4214
            | (have j0 := b4e4214 X0 x
               grind)
            | exact resolve b4e4214 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4214
          have b4e4267 : ∀ X0 : G, (k y X0) = X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e4266 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4266
          have b4e4353 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b4e4356 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e33 X0 y
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e33
            | exact resolve b4e33 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4829 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b4e124 y X0
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e124
            | exact resolve b4e124 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4843 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) ∨ (σ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e124 X0 y
               have i₂ := b4e381 (σ X0)
               grind)
            | exact superpose b4e381 b4e124
            | (have j1 := b4e381 (σ X0)
               grind)
            | exact resolve b4e124 b4e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4853 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ (σ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e4843 X0
               have i₂ := b4e409
               grind)
            | exact superpose b4e409 b4e4843
            | (have j0 := b4e4843 X0
               grind)
            | exact resolve b4e4843 b4e409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4843
          have b4e4870 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e4853 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e4853
            | (have j0 := b4e4853 X0
               grind)
            | exact resolve b4e4853 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4853
          have b4e4927 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) ∨ (τ (σ X0)) = y := by
            intro X0
            first
            | (have i₁ := b4e407 X0
               have i₂ := b4e2617 (σ X0)
               grind)
            | exact superpose b4e2617 b4e407
            | (have j1 := b4e2617 (σ X0)
               grind)
            | exact resolve b4e407 b4e2617
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2617
          have b4e4934 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e4927 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e4927
            | (have j0 := b4e4927 X0
               grind)
            | exact resolve b4e4927 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4927
          have b4e6065 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) ∨ y = (σ (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e124 X0 y
               have i₂ := b4e4870 (σ X0)
               grind)
            | exact superpose b4e4870 b4e124
            | (have j1 := b4e4870 (σ X0)
               grind)
            | exact resolve b4e124 b4e4870
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4870
          have b4e6070 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ y = (σ (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e6065 X0
               have i₂ := b4e409
               grind)
            | exact superpose b4e409 b4e6065
            | (have j0 := b4e6065 X0
               grind)
            | exact resolve b4e6065 b4e409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6065
          have b4e6074 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (σ (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e6070 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e6070
            | (have j0 := b4e6070 X0
               grind)
            | exact resolve b4e6070 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6070
          have b4e6473 : ∀ X0 X1 : G, (τ (k X1 (k X0 y))) = (k (τ X1) (k (τ X0) y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e4353 (k X0 y) X1
               have i₂ := b4e4356 X0
               grind)
            | exact superpose b4e4356 b4e4353
            | exact resolve b4e4353 b4e4356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4356
          have b4e6665 : ∀ X0 : G, (σ X0) = (σ (k y X0)) ∨ y = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e408 X0
               have i₂ := b4e4267 (σ X0)
               grind)
            | exact superpose b4e4267 b4e408
            | (have j1 := b4e4267 (σ X0)
               grind)
            | exact resolve b4e408 b4e4267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e408
          have b4e6677 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) ∨ y = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e29 X0 y
               have i₂ := b4e4267 (τ X0)
               grind)
            | exact superpose b4e4267 b4e29
            | (have j1 := b4e4267 (τ X0)
               grind)
            | exact resolve b4e29 b4e4267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4267
          have b4e6689 : ∀ X0 : G, (σ (τ X0)) = (k y X0) ∨ y = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e6677 X0
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e6677
            | (have j0 := b4e6677 X0
               grind)
            | exact resolve b4e6677 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6677
          have b4e6694 : ∀ X0 : G, y = (M.op (τ X0) y) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e6689 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e6689
            | (have j0 := b4e6689 X0
               grind)
            | exact resolve b4e6689 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6689
          have b4e6710 : ∀ X0 : G, (σ (k X0 (k y x))) = (k (σ X0) (σ x)) ∨ y = (M.op (σ x) y) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 (k y x)
               have i₂ := b4e1945
               grind)
            | exact superpose b4e1945 b4e19
            | exact resolve b4e19 b4e1945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1945
          have b4e6730 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (k y x))) ∨ y = (M.op (σ x) y) := by
            intro X0
            first
            | (have i₁ := b4e6710 X0
               have i₂ := b4e19 X0 x
               grind)
            | exact superpose b4e19 b4e6710
            | exact resolve b4e6710 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6710
          have b4e7412 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b4e355 X0 y
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e355
            | (have j0 := b4e355 X0 y
               grind)
            | (have r₁ := b4e355 y y
               have r₂ := b4e131 y
               grind)
            | exact resolve b4e355 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e7866 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 y))) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 (k X0 y)
               have i₂ := b4e4934 X0
               grind)
            | exact superpose b4e4934 b4e19
            | (have j1 := b4e4934 X0
               grind)
            | exact resolve b4e19 b4e4934
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4934
          have b4e7894 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 y))) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e7866 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e7866
            | (have j0 := b4e7866 X0 X1
               grind)
            | exact resolve b4e7866 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7866
          have b4e8508 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) ∨ y = (σ (σ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b4e124 X0 y
               have i₂ := b4e6074 (σ X0)
               grind)
            | exact superpose b4e6074 b4e124
            | (have j1 := b4e6074 (σ X0)
               grind)
            | exact resolve b4e124 b4e6074
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6074
          have b4e8513 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ y = (σ (σ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b4e8508 X0
               have i₂ := b4e409
               grind)
            | exact superpose b4e409 b4e8508
            | (have j0 := b4e8508 X0
               grind)
            | exact resolve b4e8508 b4e409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8508
          have b4e8519 : ∀ X0 : G, y = (σ (σ (σ X0))) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e8513 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e8513
            | (have j0 := b4e8513 X0
               grind)
            | exact resolve b4e8513 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8513
          have b4e8643 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op X0 (M.op X1 y)) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e93 X1 (M.op X0 (M.op X1 y))
               have i₂ := b4e40 X0 (M.op X1 y)
               grind)
            | exact superpose b4e40 b4e93
            | exact resolve b4e93 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e8667 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op (M.op X1 y) X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 (M.op (M.op X1 y) X0) X1
               have i₂ := b4e93 X1 X0
               grind)
            | exact superpose b4e93 b4e40
            | exact resolve b4e40 b4e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9034 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op X0 y)) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 (M.op X1 X0) (M.op X1 y)
               have i₂ := b4e94 X1 X0
               grind)
            | exact superpose b4e94 b4e40
            | exact resolve b4e40 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9271 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op y y) (M.op X0 y)) (M.op X1 y)) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e102 (M.op (M.op y y) (M.op X0 y)) X1
               have i₂ := b4e39 y X0
               grind)
            | exact superpose b4e39 b4e102
            | exact resolve b4e102 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e9346 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op y X0) y) (M.op X1 y)) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e9271 X0 X1
               have i₂ := b4e9034 X0 y
               grind)
            | exact superpose b4e9034 b4e9271
            | exact resolve b4e9271 b4e9034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9271
          have b4e9407 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op y X0) X1) y) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e9346 X0 X1
               have i₂ := b4e9034 X1 (M.op y X0)
               grind)
            | exact superpose b4e9034 b4e9346
            | exact resolve b4e9346 b4e9034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9346
          have b4e9440 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e9407 X0 X1
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e9407
            | exact resolve b4e9407 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9407
          have b4e9720 : ∀ X0 X1 : G, y ≠ X0 ∨ y = X1 ∨ (k (M.op (M.op X1 X0) y) X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e697 (M.op (M.op X0 X1) y) X0
               have i₂ := b4e9440 X0 X1
               grind)
            | exact superpose b4e9440 b4e697
            | (have j0 := b4e697 X0 X1
               grind)
            | (have r₁ := b4e697 (M.op (M.op X0 y) y) X0
               have r₂ := b4e9440 X0 y
               grind)
            | exact resolve b4e697 b4e9440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e697
          have b4e10491 : ∀ X0 : G, y ≠ y ∨ y = (k y (τ X0)) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e355 y (τ X0)
               have i₂ := b4e6694 X0
               grind)
            | exact superpose b4e6694 b4e355
            | (have j0 := b4e355 y (τ X0)
               have j1 := b4e6694 X0
               grind)
            | (have r₁ := b4e355 y (τ X0)
               have r₂ := b4e6694 X0
               grind)
            | exact resolve b4e355 b4e6694
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6694
          have b4e10493 : ∀ X0 : G, y = (k y (τ X0)) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e10491 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10491
          have b4e11246 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e29 X0 y
               have i₂ := b4e10493 X0
               grind)
            | exact superpose b4e10493 b4e29
            | (have j1 := b4e10493 X0
               grind)
            | exact resolve b4e29 b4e10493
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10493
          have b4e11269 : ∀ X0 : G, y = (k y X0) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e11246 X0
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e11246
            | (have j0 := b4e11246 X0
               grind)
            | exact resolve b4e11246 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11246
          have b4e11533 : ∀ X0 : G, y ≠ X0 ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e11269 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11269
          have b4e11552 : ∀ X0 : G, (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e11533 X0
               have j1 := b4e993 X0
               grind)
            | (have r₁ := b4e11533 (k y y)
               have r₂ := b4e993 y
               grind)
            | (have r₁ := b4e11533 x
               have r₂ := b4e993 x
               grind)
            | (have r₁ := b4e11533 y
               have r₂ := b4e993 y
               grind)
            | exact resolve b4e11533 b4e993
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e993 b4e11533
          have b4e12907 : ∀ X0 : G, (k y y) = (σ (k (σ (σ X0)) y)) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e407 (σ (σ X0))
               have i₂ := b4e8519 X0
               grind)
            | exact superpose b4e8519 b4e407
            | (have j1 := b4e8519 X0
               grind)
            | exact resolve b4e407 b4e8519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8519
          have b4e12916 : ∀ X0 : G, (k y y) = (σ (σ (k (σ X0) y))) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e12907 X0
               have i₂ := b4e407 (σ X0)
               grind)
            | exact superpose b4e407 b4e12907
            | (have j0 := b4e12907 X0
               grind)
            | exact resolve b4e12907 b4e407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12907
          have b4e12939 : ∀ X0 : G, (k y y) = (σ (σ (σ (k X0 y)))) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e12916 X0
               have i₂ := b4e407 X0
               grind)
            | exact superpose b4e407 b4e12916
            | (have j0 := b4e12916 X0
               grind)
            | exact resolve b4e12916 b4e407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e407 b4e12916
          have b4e12949 : ∀ X0 : G, (M.op y y) = (σ (σ (σ (k X0 y)))) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e12939 X0
               have i₂ := b4e46 y
               grind)
            | exact superpose b4e46 b4e12939
            | (have j0 := b4e12939 X0
               grind)
            | exact resolve b4e12939 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12939
          have b4e12956 : ∀ X0 : G, y = (σ (σ (σ (k X0 y)))) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e12949 X0
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e12949
            | (have j0 := b4e12949 X0
               grind)
            | exact resolve b4e12949 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12949
          have b4e13405 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y (M.op (M.op y (σ y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e172 (M.op (M.op y (σ y)) X0)
               have i₂ := b4e145 y X0
               grind)
            | exact superpose b4e145 b4e172
            | (have j0 := b4e172 X0
               grind)
            | exact resolve b4e172 b4e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e145 b4e172
          have b4e13411 : ∀ X0 : G, y = (M.op (M.op y (σ y)) X0) ∨ y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13405 X0
               have i₂ := b4e11552 (M.op (M.op y (σ y)) X0)
               grind)
            | exact superpose b4e11552 b4e13405
            | (have j0 := b4e13405 X0
               grind)
            | exact resolve b4e13405 b4e11552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13405
          have b4e13532 : ∀ X0 : G, y = (M.op (M.op y y) X0) ∨ y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13411 X0
               have i₂ := b4e148 y
               grind)
            | exact superpose b4e148 b4e13411
            | (have j0 := b4e13411 X0
               grind)
            | exact resolve b4e13411 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148 b4e13411
          have b4e13636 : ∀ X0 : G, y = (M.op y X0) ∨ y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13532 X0
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e13532
            | (have j0 := b4e13532 X0
               grind)
            | (have r₁ := b4e13532 y
               have r₂ := b4e188 y
               grind)
            | exact resolve b4e13532 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13532
          have b4e13710 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e13636 X0
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e13636
            | (have j0 := b4e13636 X0
               grind)
            | (have r₁ := b4e13636 y
               have r₂ := b4e131 y
               grind)
            | exact resolve b4e13636 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13636
          have b4e13880 : ∀ X0 : G, y ≠ X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13710 (M.op X0 y)
               have i₂ := b4e101 X0
               grind)
            | exact superpose b4e101 b4e13710
            | (have j0 := b4e13710 (M.op X0 y)
               grind)
            | (have r₁ := b4e13710 (M.op y y)
               have r₂ := b4e101 y
               grind)
            | exact resolve b4e13710 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e15483 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 y) (M.op X2 y)) X1) = X2 ∨ y = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e534 X0 X1 X1 X2
               have i₂ := b4e40 X0 X1
               grind)
            | exact superpose b4e40 b4e534
            | (have j0 := b4e534 X0 X1 X2 x
               grind)
            | exact resolve b4e534 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e534
          have b4e15770 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) y) X1) = X2 ∨ y = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e15483 X0 X1 X2
               have i₂ := b4e9034 X2 X0
               grind)
            | exact superpose b4e9034 b4e15483
            | (have j0 := b4e15483 X0 X1 X2
               grind)
            | exact resolve b4e15483 b4e9034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15483
          have b4e26999 : ∀ X0 X1 : G, y ≠ (M.op (M.op X0 y) X1) ∨ y = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13710 (M.op X0 (M.op X1 y))
               have i₂ := b4e8643 X0 X1
               grind)
            | exact superpose b4e8643 b4e13710
            | (have j0 := b4e13710 (M.op X0 (M.op X1 y))
               grind)
            | exact resolve b4e13710 b4e8643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39217 : ∀ X0 : G, (τ y) = (σ (σ (k X0 y))) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e14 (σ (σ (k X0 y)))
               have i₂ := b4e12956 X0
               grind)
            | exact superpose b4e12956 b4e14
            | (have j1 := b4e12956 X0
               grind)
            | exact resolve b4e14 b4e12956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12956
          have b4e39281 : ∀ X0 : G, y = (σ (σ (k X0 y))) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e39217 X0
               have i₂ := b4e409
               grind)
            | exact superpose b4e409 b4e39217
            | (have j0 := b4e39217 X0
               grind)
            | exact resolve b4e39217 b4e409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39217
          have b4e39644 : ∀ X0 : G, (σ (k X0 y)) = (τ y) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e14 (σ (k X0 y))
               have i₂ := b4e39281 X0
               grind)
            | exact superpose b4e39281 b4e14
            | (have j1 := b4e39281 X0
               grind)
            | exact resolve b4e14 b4e39281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39281
          have b4e39710 : ∀ X0 : G, y = (σ (k X0 y)) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e39644 X0
               have i₂ := b4e409
               grind)
            | exact superpose b4e409 b4e39644
            | (have j0 := b4e39644 X0
               grind)
            | exact resolve b4e39644 b4e409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39644
          have b4e40881 : ∀ X0 : G, (k X0 y) = (τ y) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e14 (k X0 y)
               have i₂ := b4e39710 X0
               grind)
            | exact superpose b4e39710 b4e14
            | (have j1 := b4e39710 X0
               grind)
            | exact resolve b4e14 b4e39710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39710
          have b4e40950 : ∀ X0 : G, y = (k X0 y) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e40881 X0
               have i₂ := b4e409
               grind)
            | exact superpose b4e409 b4e40881
            | (have j0 := b4e40881 X0
               grind)
            | exact resolve b4e40881 b4e409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40881
          have b4e42067 : ∀ X0 : G, y ≠ X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b4e40950 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40950
          have b4e42076 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b4e42067 X0
               have j1 := b4e381 X0
               grind)
            | (have r₁ := b4e42067 (k y y)
               have r₂ := b4e381 y
               grind)
            | (have r₁ := b4e42067 X0
               have r₂ := b4e381 X0
               grind)
            | (have r₁ := b4e42067 y
               have r₂ := b4e381 y
               grind)
            | exact resolve b4e42067 b4e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e381 b4e42067
          have b4e256410 : ∀ X0 X1 : G, y = X0 ∨ y = X1 ∨ (M.op (M.op (M.op X1 X0) y) X1) = (k (M.op (M.op X1 X0) y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e188 (M.op (M.op X1 X0) y)
               have i₂ := b4e15770 X1 (M.op (M.op X1 X0) y) X0
               grind)
            | exact superpose b4e15770 b4e188
            | (have j1 := b4e15770 X1 (M.op (M.op X1 X0) y) x
               grind)
            | exact resolve b4e188 b4e15770
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15770
          have b4e256628 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) y) X1) = X0 ∨ y = X0 ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e256410 X0 X1
               have i₂ := b4e9440 X1 X0
               grind)
            | exact superpose b4e9440 b4e256410
            | (have j0 := b4e256410 X0 X0
               grind)
            | exact resolve b4e256410 b4e9440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e256410
          have b4e256737 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) y) X1) = X0 ∨ y = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e256628 X0 X1
               have j1 := b4e9720 X0 X1
               grind)
            | (have r₁ := b4e256628 y X1
               have r₂ := b4e9720 (k (M.op (M.op X1 y) y) X1) X1
               grind)
            | (have r₁ := b4e256628 X0 X1
               have r₂ := b4e9720 X0 X1
               grind)
            | (have r₁ := b4e256628 y X1
               have r₂ := b4e9720 y X1
               grind)
            | exact resolve b4e256628 b4e9720
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9720 b4e256628
          have b4e256801 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 y) y) X1) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e256737 (M.op X0 X1) X1
               have i₂ := b4e40 X0 X1
               grind)
            | exact superpose b4e40 b4e256737
            | (have j0 := b4e256737 X0 X1
               grind)
            | exact resolve b4e256737 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e256999 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op (M.op (σ X1) X0) y)) X1) ∨ (σ X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b4e33 (M.op (M.op (σ X1) X0) y) X1
               have i₂ := b4e256737 X0 (σ X1)
               grind)
            | exact superpose b4e256737 b4e33
            | (have j1 := b4e256737 X0 (σ X1)
               grind)
            | exact resolve b4e33 b4e256737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e256737
          have b4e257161 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e256801 X0 X1
               have i₂ := b4e101 X0
               grind)
            | exact superpose b4e101 b4e256801
            | (have j0 := b4e256801 X0 X1
               grind)
            | exact resolve b4e256801 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e256801
          have b4e257381 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b4e33 X0 X1
               have i₂ := b4e257161 X0 (σ X1)
               grind)
            | exact superpose b4e257161 b4e33
            | (have j1 := b4e257161 X0 (σ X1)
               grind)
            | exact resolve b4e33 b4e257161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e257398 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 (k y x))) ∨ y = (M.op (σ x) y) ∨ y = (k y x) := by
            intro X0
            first
            | (have i₁ := b4e6730 X0
               have i₂ := b4e257161 X0 (k y x)
               grind)
            | exact superpose b4e257161 b4e6730
            | (have j1 := b4e257161 X0 (M.op (σ x) y)
               grind)
            | exact resolve b4e6730 b4e257161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6730
          have b4e257403 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 (k X1 y))) ∨ y = X1 ∨ y = (k X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e7894 X1 X0
               have i₂ := b4e257161 X0 (k X1 y)
               grind)
            | exact superpose b4e257161 b4e7894
            | (have j0 := b4e7894 X1 X1
               have j1 := b4e257161 X0 X1
               grind)
            | exact resolve b4e7894 b4e257161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7894
          have b4e257419 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e257161 (σ X0) (σ X1)
               grind)
            | exact superpose b4e257161 b4e19
            | (have j1 := b4e257161 X0 (σ X1)
               grind)
            | exact resolve b4e19 b4e257161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257161
          have b4e257662 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 (k X1 y))) ∨ y = (k X1 y) := by
            intro X0 X1
            first
            | (have j0 := b4e257403 X0 X1
               have j1 := b4e7412 X1
               grind)
            | (have r₁ := b4e257403 X0 X0
               have r₂ := b4e7412 X0
               grind)
            | (have r₁ := b4e257403 X0 y
               have r₂ := b4e7412 y
               grind)
            | (have r₁ := b4e257403 X0 X1
               have r₂ := b4e7412 (k X1 y)
               grind)
            | exact resolve b4e257403 b4e7412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7412 b4e257403
          have b4e257667 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ y = (M.op (σ x) y) ∨ y = (k y x) := by
            intro X0
            first
            | (have i₁ := b4e257398 X0
               have i₂ := b4e11552 x
               grind)
            | exact superpose b4e11552 b4e257398
            | exact resolve b4e257398 b4e11552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257398
          have b4e257730 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ y = (k X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e257662 X0 X1
               have i₂ := b4e42076 X1
               grind)
            | exact superpose b4e42076 b4e257662
            | (have j0 := b4e257662 X0 X1
               grind)
            | exact resolve b4e257662 b4e42076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257662
          have b4e257735 : ∀ X0 : G, x = y ∨ (σ (k X0 x)) = (σ (M.op X0 x)) ∨ y = (M.op (σ x) y) := by
            intro X0
            first
            | (have i₁ := b4e257667 X0
               have i₂ := b4e11552 x
               grind)
            | exact superpose b4e11552 b4e257667
            | (have j0 := b4e257667 X0
               grind)
            | exact resolve b4e257667 b4e11552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257667
          have b4e257763 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e257730 X0 X1
               have i₂ := b4e42076 X1
               grind)
            | exact superpose b4e42076 b4e257730
            | (have j0 := b4e257730 X0 X1
               grind)
            | exact resolve b4e257730 b4e42076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257730
          have b4e257765 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ y = (M.op (σ x) y) := by
            intro X0
            first
            | (have j0 := b4e257735 X0
               grind)
            | (have r₁ := b4e257735 X0
               have r₂ := b4e182
               grind)
            | exact resolve b4e257735 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257735
          have b4e258004 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (k (σ (M.op X0 X1)) (σ X2)) ∨ y = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e19 (k X0 X1) X2
               have i₂ := b4e257763 X0 X1
               grind)
            | exact superpose b4e257763 b4e19
            | (have j1 := b4e257763 X0 X1
               grind)
            | exact resolve b4e19 b4e257763
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257763
          have b4e258107 : ∀ X0 X1 X2 : G, (σ (k (k X0 X1) X2)) = (σ (k (M.op X0 X1) X2)) ∨ y = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e258004 X0 X1 X2
               have i₂ := b4e19 (M.op X0 X1) X2
               grind)
            | exact superpose b4e19 b4e258004
            | (have j0 := b4e258004 X0 X1 X2
               grind)
            | exact resolve b4e258004 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e258004
          have b4e262914 : ∀ X0 X1 : G, (k (τ X1) (k y X0)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = y ∨ y = (M.op (σ X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e257381 X0 (k y X0)
               have i₂ := b4e6665 X0
               grind)
            | exact superpose b4e6665 b4e257381
            | (have j0 := b4e257381 X0 X0
               have j1 := b4e6665 X0
               grind)
            | exact resolve b4e257381 b4e6665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6665 b4e257381
          have b4e263162 : ∀ X0 X1 : G, (k (τ X1) (k y X0)) = (τ (M.op X1 (σ X0))) ∨ y = (M.op (σ X0) y) := by
            intro X0 X1
            first
            | (have j0 := b4e262914 X0 X1
               have j1 := b4e13880 (σ X0)
               grind)
            | (have r₁ := b4e262914 X0 X1
               have r₂ := b4e13880 (σ X0)
               grind)
            | (have r₁ := b4e262914 X0 X1
               have r₂ := b4e13880 (M.op (σ X0) y)
               grind)
            | exact resolve b4e262914 b4e13880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e262914
          have b4e263249 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ y = (M.op (σ X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e263162 X0 X1
               have i₂ := b4e11552 X0
               grind)
            | exact superpose b4e11552 b4e263162
            | (have j0 := b4e263162 X0 X1
               grind)
            | exact resolve b4e263162 b4e11552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e263162
          have b4e264683 : ∀ X0 X1 : G, (M.op (σ X0) y) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b4e40 (σ X0) (σ X1)
               have i₂ := b4e257419 X0 X1
               grind)
            | exact superpose b4e257419 b4e40
            | (have j1 := b4e257419 X0 X1
               grind)
            | exact resolve b4e40 b4e257419
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257419
          have b4e272184 : ∀ X0 : G, (k X0 x) = (τ (σ (M.op X0 x))) ∨ y = (M.op (σ x) y) := by
            intro X0
            first
            | (have i₁ := b4e14 (k X0 x)
               have i₂ := b4e257765 X0
               grind)
            | exact superpose b4e257765 b4e14
            | exact resolve b4e14 b4e257765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257765
          have b4e272274 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = (M.op (σ x) y) := by
            intro X0
            first
            | (have i₁ := b4e272184 X0
               have i₂ := b4e14 (M.op X0 x)
               grind)
            | exact superpose b4e14 b4e272184
            | exact resolve b4e272184 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272184
          have b4e272734 : ∀ X0 : G, y ≠ y ∨ y = (σ x) ∨ (M.op X0 x) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e13710 (σ x)
               have i₂ := b4e272274 X0
               grind)
            | exact superpose b4e272274 b4e13710
            | (have j0 := b4e13710 (σ x)
               have j1 := b4e272274 X0
               grind)
            | (have r₁ := b4e13710 (σ x)
               have r₂ := b4e272274 X0
               grind)
            | exact resolve b4e13710 b4e272274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272274
          have b4e272760 : ∀ X0 : G, y = (σ x) ∨ (M.op X0 x) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e272734 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272734
          have b4e272779 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e272760 X0
               grind)
            | (have r₁ := b4e272760 X0
               have r₂ := b4e402
               grind)
            | exact resolve b4e272760 b4e402
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272760
          have b4e273129 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) x)) := by
            intro X0
            first
            | (have i₁ := b4e124 X0 x
               have i₂ := b4e272779 (σ X0)
               grind)
            | exact superpose b4e272779 b4e124
            | exact resolve b4e124 b4e272779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e273137 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b4e28 X0 x
               have i₂ := b4e272779 (τ X0)
               grind)
            | exact superpose b4e272779 b4e28
            | exact resolve b4e28 b4e272779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e285797 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op (σ x) X0) y)) x) ∨ y = (σ x) := by
            intro X0
            first
            | (have i₁ := b4e272779 (τ (M.op (M.op (σ x) X0) y))
               have i₂ := b4e256999 X0 x
               grind)
            | exact superpose b4e256999 b4e272779
            | (have j1 := b4e256999 X0 x
               grind)
            | exact resolve b4e272779 b4e256999
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e285833 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op (σ x) X0) y)) x) := by
            intro X0
            first
            | (have j0 := b4e285797 X0
               grind)
            | (have r₁ := b4e285797 X0
               have r₂ := b4e402
               grind)
            | exact resolve b4e285797 b4e402
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e285797
          have b4e286216 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (M.op (τ (M.op (M.op X0 y) y)) x) := by
            intro X0
            first
            | (have i₁ := b4e285833 (M.op X0 (σ x))
               have i₂ := b4e40 X0 (σ x)
               grind)
            | exact superpose b4e40 b4e285833
            | exact resolve b4e285833 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e286265 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ (M.op (M.op (σ x) X0) y)) y) := by
            intro X0
            first
            | (have i₁ := b4e40 (τ (M.op (M.op (σ x) X0) y)) x
               have i₂ := b4e285833 X0
               grind)
            | exact superpose b4e285833 b4e40
            | exact resolve b4e40 b4e285833
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e285833
          have b4e286311 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e286216 X0
               have i₂ := b4e101 X0
               grind)
            | exact superpose b4e101 b4e286216
            | exact resolve b4e286216 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e286216
          have b4e286534 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (M.op (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op X0 (σ x))
               have i₂ := b4e286311 X0
               grind)
            | exact superpose b4e286311 b4e15
            | exact resolve b4e15 b4e286311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e286924 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e286534 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e286534
            | exact resolve b4e286534 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e286956 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e273137 X0
               have i₂ := b4e286534 X0
               grind)
            | exact superpose b4e286534 b4e273137
            | exact resolve b4e273137 b4e286534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e273137 b4e286534
          have b4e287434 : ∀ X0 : G, (k X0 (σ (σ x))) = (σ (M.op (τ X0) (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e28 X0 (σ x)
               have i₂ := b4e286956 (τ X0)
               grind)
            | exact superpose b4e286956 b4e28
            | exact resolve b4e28 b4e286956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e287882 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op (σ (M.op X0 x)) y)) X0) ∨ (σ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e256999 (σ x) X0
               have i₂ := b4e286924 X0
               grind)
            | exact superpose b4e286924 b4e256999
            | (have j0 := b4e256999 X0 X0
               grind)
            | exact resolve b4e256999 b4e286924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e256999
          have b4e287886 : ∀ X0 : G, (M.op (σ X0) y) = (M.op (σ x) (σ (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b4e40 (σ X0) (σ x)
               have i₂ := b4e286924 X0
               grind)
            | exact superpose b4e286924 b4e40
            | exact resolve b4e40 b4e286924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e287894 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op X0 x)) y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e9440 (σ X0) (σ x)
               have i₂ := b4e286924 X0
               grind)
            | exact superpose b4e286924 b4e9440
            | exact resolve b4e9440 b4e286924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e287933 : ∀ X0 : G, x = (k (τ (M.op (σ (M.op X0 x)) y)) X0) ∨ (σ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e287882 X0
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e287882
            | (have j0 := b4e287882 X0
               grind)
            | exact resolve b4e287882 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287882
          have b4e288768 : ∀ X0 : G, (M.op (k X0 (σ (σ x))) (σ x)) = (σ (M.op (M.op (τ X0) (σ x)) x)) := by
            intro X0
            first
            | (have i₁ := b4e286924 (M.op (τ X0) (σ x))
               have i₂ := b4e287434 X0
               grind)
            | exact superpose b4e287434 b4e286924
            | exact resolve b4e286924 b4e287434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287434
          have b4e288922 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ (M.op (M.op x X0) y)) y) := by
            intro X0
            first
            | (have i₁ := b4e287886 (M.op (M.op x X0) y)
               have i₂ := b4e9440 x X0
               grind)
            | exact superpose b4e9440 b4e287886
            | exact resolve b4e287886 b4e9440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e288973 : ∀ X0 : G, y ≠ (M.op (σ X0) y) ∨ y = (k (σ (M.op X0 x)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e355 (σ (M.op X0 x)) (σ x)
               have i₂ := b4e287886 X0
               grind)
            | exact superpose b4e287886 b4e355
            | (have j0 := b4e355 y (σ X0)
               grind)
            | exact resolve b4e355 b4e287886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e288998 : ∀ X0 : G, y = (σ (k (M.op X0 x) x)) ∨ y ≠ (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e288973 X0
               have i₂ := b4e19 (M.op X0 x) x
               grind)
            | exact superpose b4e19 b4e288973
            | (have j0 := b4e288973 X0
               grind)
            | exact resolve b4e288973 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e288973
          have b4e289027 : ∀ X0 : G, y ≠ (M.op (σ X0) y) ∨ y = (σ (M.op (M.op X0 x) x)) := by
            intro X0
            first
            | (have i₁ := b4e288998 X0
               have i₂ := b4e272779 (M.op X0 x)
               grind)
            | exact superpose b4e272779 b4e288998
            | (have j0 := b4e288998 X0
               grind)
            | exact resolve b4e288998 b4e272779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e288998
          have b4e289161 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op X0 y)) y) (σ (M.op (M.op x y) X0))) := by
            intro X0
            first
            | (have i₁ := b4e287894 (M.op (M.op x y) X0)
               have i₂ := b4e93 x X0
               grind)
            | exact superpose b4e93 b4e287894
            | exact resolve b4e287894 b4e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e291137 : ∀ X0 : G, (τ (M.op (M.op (σ x) X0) y)) = (M.op (M.op x (τ X0)) y) := by
            intro X0
            first
            | (have i₁ := b4e101 (τ (M.op (M.op (σ x) X0) y))
               have i₂ := b4e286265 X0
               grind)
            | exact superpose b4e286265 b4e101
            | exact resolve b4e101 b4e286265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e286265
          have b4e292347 : ∀ X0 : G, (M.op (M.op (σ x) X0) y) = (σ (M.op (M.op x (τ X0)) y)) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op (M.op (σ x) X0) y)
               have i₂ := b4e291137 X0
               grind)
            | exact superpose b4e291137 b4e15
            | exact resolve b4e15 b4e291137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e291137
          have b4e293876 : ∀ X0 : G, y ≠ (M.op (σ x) (σ X0)) ∨ y = (σ (M.op (M.op (M.op (M.op x X0) y) x) x)) := by
            intro X0
            first
            | (have i₁ := b4e289027 (M.op (M.op x X0) y)
               have i₂ := b4e288922 X0
               grind)
            | exact superpose b4e288922 b4e289027
            | (have j0 := b4e289027 (M.op (M.op x X0) y)
               grind)
            | exact resolve b4e289027 b4e288922
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e288922 b4e289027
          have b4e293885 : ∀ X0 : G, y ≠ (M.op (σ x) (σ X0)) ∨ y = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e293876 X0
               have i₂ := b4e9440 x X0
               grind)
            | exact superpose b4e9440 b4e293876
            | (have j0 := b4e293876 X0
               grind)
            | exact resolve b4e293876 b4e9440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293876
          have b4e294040 : ∀ X0 : G, y ≠ (M.op (σ x) (M.op (M.op (σ x) X0) y)) ∨ y = (σ (M.op (M.op (M.op x (τ X0)) y) x)) := by
            intro X0
            first
            | (have i₁ := b4e293885 (M.op (M.op x (τ X0)) y)
               have i₂ := b4e292347 X0
               grind)
            | exact superpose b4e292347 b4e293885
            | (have j0 := b4e293885 (M.op (M.op x (τ X0)) y)
               grind)
            | exact resolve b4e293885 b4e292347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292347 b4e293885
          have b4e294255 : ∀ X0 : G, (σ (τ X0)) = y ∨ y ≠ (M.op (σ x) (M.op (M.op (σ x) X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e294040 X0
               have i₂ := b4e9440 x (τ X0)
               grind)
            | exact superpose b4e9440 b4e294040
            | (have j0 := b4e294040 X0
               grind)
            | exact resolve b4e294040 b4e9440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e294040
          have b4e294287 : ∀ X0 : G, y ≠ (M.op (σ x) (M.op (M.op (σ x) X0) y)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e294255 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e294255
            | (have j0 := b4e294255 X0
               grind)
            | exact resolve b4e294255 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e294255
          have b4e295015 : y ≠ (M.op (σ x) (M.op y y)) ∨ y = (σ x) := by
            first
            | (have i₁ := b4e294287 (σ x)
               have i₂ := b4e188 (σ x)
               grind)
            | exact superpose b4e188 b4e294287
            | (have j0 := b4e294287 (σ x)
               grind)
            | exact resolve b4e294287 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e294287
          have b4e295065 : y ≠ (M.op (σ x) (M.op y y)) := by
            first
            | (have r₁ := b4e295015
               have r₂ := b4e402
               grind)
            | exact resolve b4e295015 b4e402
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e295015
          have b4e295072 : y ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e295065
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e295065
            | exact resolve b4e295065 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e295065
          have b4e304586 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e263249 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e263249
            | exact resolve b4e263249 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e263249
          have b4e304838 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e304586 X0 X1
               have i₂ := b4e4353 X0 X1
               grind)
            | exact superpose b4e4353 b4e304586
            | (have j0 := b4e304586 X0 X1
               grind)
            | exact resolve b4e304586 b4e4353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e304586
          have b4e305101 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ y = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (k X0 X1)
               have i₂ := b4e304838 X1 X0
               grind)
            | exact superpose b4e304838 b4e15
            | (have j1 := b4e304838 X1 X1
               grind)
            | exact resolve b4e15 b4e304838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e304838
          have b4e305220 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ y = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e305101 X0 X1
               have i₂ := b4e15 (M.op X0 X1)
               grind)
            | exact superpose b4e15 b4e305101
            | (have j0 := b4e305101 X0 X1
               grind)
            | exact resolve b4e305101 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e305101
          have b4e308006 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ y = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e264683 (τ X0) (τ X1)
               have i₂ := b4e4353 X1 X0
               grind)
            | exact superpose b4e4353 b4e264683
            | (have j0 := b4e264683 X0 (τ X1)
               grind)
            | exact resolve b4e264683 b4e4353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e264683
          have b4e308295 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (M.op (σ (τ X1)) (k X0 X1)) ∨ y = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e308006 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e308006
            | (have j0 := b4e308006 X0 X1
               grind)
            | exact resolve b4e308006 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308006
          have b4e308378 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (M.op X1 (k X0 X1)) ∨ y = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e308295 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e308295
            | (have j0 := b4e308295 X0 X1
               grind)
            | exact resolve b4e308295 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308295
          have b4e308427 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (k X0 X1)) ∨ y = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e308378 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e308378
            | (have j0 := b4e308378 X0 X1
               grind)
            | exact resolve b4e308378 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308378
          have b4e308453 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (k X0 X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e308427 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e308427
            | (have j0 := b4e308427 X0 X1
               grind)
            | exact resolve b4e308427 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308427
          have b4e308664 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (k X0 X1) (M.op X0 y)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X1 (k X0 X1)
               have i₂ := b4e308453 X0 X1
               grind)
            | exact superpose b4e308453 b4e40
            | (have j1 := b4e308453 X0 X1
               grind)
            | exact resolve b4e40 b4e308453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e308665 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op X1 y)) = (M.op (k X0 X1) y) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e94 X1 (k X0 X1)
               have i₂ := b4e308453 X0 X1
               grind)
            | exact superpose b4e308453 b4e94
            | (have j1 := b4e308453 X0 X1
               grind)
            | exact resolve b4e94 b4e308453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308453
          have b4e308770 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (k X0 X1) y) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e308665 X0 X1
               have i₂ := b4e9034 X1 X0
               grind)
            | exact superpose b4e9034 b4e308665
            | (have j0 := b4e308665 X0 X1
               grind)
            | exact resolve b4e308665 b4e9034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308665
          have b4e309401 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (k X1 X0) y)) = X1 ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e102 (k X1 X0) X1
               have i₂ := b4e308664 X1 X0
               grind)
            | exact superpose b4e308664 b4e102
            | (have j1 := b4e308664 X0 X0
               grind)
            | exact resolve b4e102 b4e308664
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e309403 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op (M.op (k X1 X0) y) X1) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e8643 (k X1 X0) X1
               have i₂ := b4e308664 X1 X0
               grind)
            | exact superpose b4e308664 b4e8643
            | (have j1 := b4e308664 X0 X0
               grind)
            | exact resolve b4e8643 b4e308664
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308664
          have b4e309489 : ∀ X0 X1 : G, (M.op (M.op (k X1 X0) y) X1) = X0 ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e309403 X0 X1
               have i₂ := b4e101 X0
               grind)
            | exact superpose b4e101 b4e309403
            | (have j0 := b4e309403 X0 X1
               grind)
            | exact resolve b4e309403 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e309403
          have b4e309490 : ∀ X0 X1 : G, (M.op (M.op X0 (k X1 X0)) y) = X1 ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e309401 X0 X1
               have i₂ := b4e9034 (k X1 X0) X0
               grind)
            | exact superpose b4e9034 b4e309401
            | (have j0 := b4e309401 X0 X1
               grind)
            | exact resolve b4e309401 b4e9034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e309401
          have b4e309823 : ∀ X0 X1 : G, (M.op (M.op (k (M.op X1 y) X0) X1) y) = X0 ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e9034 X1 (k (M.op X1 y) X0)
               have i₂ := b4e309489 X0 (M.op X1 y)
               grind)
            | exact superpose b4e309489 b4e9034
            | (have j1 := b4e309489 X0 X1
               grind)
            | exact resolve b4e9034 b4e309489
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e309489
          have b4e311063 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X2) = (M.op (M.op (M.op (M.op X0 X1) y) (M.op X2 y)) y) ∨ y = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e517 X2 (k X0 X1)
               have i₂ := b4e308770 X0 X1
               grind)
            | exact superpose b4e308770 b4e517
            | (have j1 := b4e308770 X0 X1
               grind)
            | exact resolve b4e517 b4e308770
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e311096 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X1) y) y) (k X0 X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e9440 (k X0 X1) y
               have i₂ := b4e308770 X0 X1
               grind)
            | exact superpose b4e308770 b4e9440
            | (have j1 := b4e308770 X0 (M.op (M.op (M.op (M.op X0 X1) y) y) (k X0 X1))
               grind)
            | exact resolve b4e9440 b4e308770
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308770
          have b4e311132 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) (k X0 X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e311096 X0 X1
               have i₂ := b4e101 (M.op X0 X1)
               grind)
            | exact superpose b4e101 b4e311096
            | (have j0 := b4e311096 X0 (M.op (M.op X0 X1) (k X0 X1))
               grind)
            | exact resolve b4e311096 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311096
          have b4e311141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (k X0 X1) X2) ∨ y = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e311063 X0 X1 X2
               have i₂ := b4e517 X2 (M.op X0 X1)
               grind)
            | exact superpose b4e517 b4e311063
            | (have j0 := b4e311063 X0 X1 X2
               grind)
            | exact resolve b4e311063 b4e517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311063
          have b4e311284 : ∀ X0 X1 : G, y = (M.op X0 (k (M.op (M.op X1 X0) y) X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e311132 (M.op (M.op X1 X0) y) X1
               have i₂ := b4e9440 X1 X0
               grind)
            | exact superpose b4e9440 b4e311132
            | (have j0 := b4e311132 X0 (M.op X0 (k (M.op (M.op X1 X0) y) X1))
               grind)
            | exact resolve b4e311132 b4e9440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e311483 : ∀ X0 X1 : G, y ≠ y ∨ y = (k (k X0 X1) (M.op X0 X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e355 (k X0 X1) (M.op X0 X1)
               have i₂ := b4e311132 X0 X1
               grind)
            | exact superpose b4e311132 b4e355
            | (have j0 := b4e355 (k X0 X1) (M.op X0 X1)
               have j1 := b4e311132 X0 (k (k X0 X1) (M.op X0 X1))
               grind)
            | (have r₁ := b4e355 (k X0 X1) (M.op X0 X1)
               have r₂ := b4e311132 X0 X1
               grind)
            | (have r₁ := b4e355 X0 X1
               have r₂ := b4e311132 X0 (M.op X1 X0)
               grind)
            | exact resolve b4e355 b4e311132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311132
          have b4e311502 : ∀ X0 X1 : G, y = (k (k X0 X1) (M.op X0 X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e311483 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311483
          have b4e311938 : ∀ X0 X1 : G, y = (k (k (M.op (M.op X1 X0) y) X1) X0) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e311502 (M.op (M.op X1 X0) y) X1
               have i₂ := b4e9440 X1 X0
               grind)
            | exact superpose b4e9440 b4e311502
            | (have j0 := b4e311502 X0 (k (k (M.op (M.op X1 X0) y) X1) X0)
               grind)
            | exact resolve b4e311502 b4e9440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311502
          have b4e314383 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) y) = (M.op (σ x) (σ (M.op (M.op X0 X1) x))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e287886 (k X0 X1)
               have i₂ := b4e311141 X0 X1 x
               grind)
            | exact superpose b4e311141 b4e287886
            | (have j1 := b4e311141 X0 X1 x
               grind)
            | exact resolve b4e287886 b4e311141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311141
          have b4e314476 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) y) = (M.op (σ (M.op X0 X1)) y) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e314383 X0 X1
               have i₂ := b4e287886 (M.op X0 X1)
               grind)
            | exact superpose b4e287886 b4e314383
            | (have j0 := b4e314383 X0 X1
               grind)
            | exact resolve b4e314383 b4e287886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287886 b4e314383
          have b4e314770 : ∀ X0 X1 : G, y = (M.op (M.op X0 y) (M.op (k (M.op X1 y) X0) X1)) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e9440 (M.op (k (M.op X1 y) X0) X1) y
               have i₂ := b4e309823 X0 X1
               grind)
            | exact superpose b4e309823 b4e9440
            | (have j1 := b4e309823 (M.op (M.op X0 y) (M.op (k (M.op X1 y) X0) X1)) X1
               grind)
            | exact resolve b4e9440 b4e309823
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e309823
          have b4e315551 : ∀ X0 X1 : G, (M.op (k (M.op (M.op X0 (M.op X1 y)) y) X0) y) = X1 ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (k (M.op (M.op X0 (M.op X1 y)) y) X0) X1
               have i₂ := b4e311284 (M.op X1 y) X0
               grind)
            | exact superpose b4e311284 b4e34
            | (have j1 := b4e311284 X0 X0
               grind)
            | exact resolve b4e34 b4e311284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311284
          have b4e315601 : ∀ X0 X1 : G, (M.op (k (M.op (M.op X0 y) X1) X0) y) = X1 ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e315551 X0 X1
               have i₂ := b4e8643 X0 X1
               grind)
            | exact superpose b4e8643 b4e315551
            | (have j0 := b4e315551 X0 X1
               grind)
            | exact resolve b4e315551 b4e8643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e315551
          have b4e317108 : ∀ X0 X1 : G, (σ y) = (k (σ (k (M.op (M.op X0 (τ X1)) y) X0)) X1) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e29 X1 (k (M.op (M.op X0 (τ X1)) y) X0)
               have i₂ := b4e311938 (τ X1) X0
               grind)
            | exact superpose b4e311938 b4e29
            | (have j1 := b4e311938 X0 X0
               grind)
            | exact resolve b4e29 b4e311938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311938
          have b4e317198 : ∀ X0 X1 : G, y = (k (σ (k (M.op (M.op X0 (τ X1)) y) X0)) X1) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e317108 X0 X1
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e317108
            | (have j0 := b4e317108 (k (σ (k (M.op (M.op X0 (τ X1)) y) X0)) X1) X1
               grind)
            | exact resolve b4e317108 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e317108
          have b4e320690 : ∀ X0 : G, (σ X0) = (M.op (k (σ x) (σ (M.op X0 x))) y) ∨ y = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e315601 (σ (M.op X0 x)) (σ X0)
               have i₂ := b4e287894 X0
               grind)
            | exact superpose b4e287894 b4e315601
            | (have j0 := b4e315601 (σ (M.op X0 x)) x
               grind)
            | exact resolve b4e315601 b4e287894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287894 b4e315601
          have b4e320883 : ∀ X0 : G, (σ X0) = (M.op (σ (k x (M.op X0 x))) y) ∨ y = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e320690 X0
               have i₂ := b4e19 x (M.op X0 x)
               grind)
            | exact superpose b4e19 b4e320690
            | (have j0 := b4e320690 X0
               grind)
            | exact resolve b4e320690 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e320690
          have b4e348362 : ∀ X0 X1 : G, (σ y) = (σ (k (M.op X0 X1) (k X0 X1))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e258107 X0 X1 (k X0 X1)
               have i₂ := b4e370 (k X0 X1)
               grind)
            | exact superpose b4e370 b4e258107
            | (have j0 := b4e258107 X0 X1 x
               grind)
            | exact resolve b4e258107 b4e370
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e370 b4e258107
          have b4e348565 : ∀ X0 X1 : G, y = (σ (k (M.op X0 X1) (k X0 X1))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e348362 X0 X1
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e348362
            | (have j0 := b4e348362 X0 (σ (k (M.op X0 X1) (k X0 X1)))
               grind)
            | exact resolve b4e348362 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e348362
          have b4e348844 : ∀ X0 X1 X2 : G, (τ (k y X2)) = (k (k (M.op X0 X1) (k X0 X1)) (τ X2)) ∨ y = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e124 (k (M.op X0 X1) (k X0 X1)) X2
               have i₂ := b4e348565 X0 X1
               grind)
            | exact superpose b4e348565 b4e124
            | (have j1 := b4e348565 X0 X1
               grind)
            | exact resolve b4e124 b4e348565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e348565
          have b4e348918 : ∀ X0 X1 X2 : G, (k y (τ X2)) = (k (k (M.op X0 X1) (k X0 X1)) (τ X2)) ∨ y = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e348844 X0 X1 X2
               have i₂ := b4e4829 X2
               grind)
            | exact superpose b4e4829 b4e348844
            | (have j0 := b4e348844 X0 X1 X2
               grind)
            | exact resolve b4e348844 b4e4829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4829 b4e348844
          have b4e349065 : ∀ X0 X1 X2 : G, (τ X2) = (k (k (M.op X0 X1) (k X0 X1)) (τ X2)) ∨ y = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e348918 X0 X1 X2
               have i₂ := b4e11552 (τ X2)
               grind)
            | exact superpose b4e11552 b4e348918
            | (have j0 := b4e348918 X0 X1 X2
               grind)
            | exact resolve b4e348918 b4e11552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e348918
          have b4e377860 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (k (M.op X1 X2) (k X1 X2))) X0) ∨ y = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29 X0 (k (M.op X1 X2) (k X1 X2))
               have i₂ := b4e349065 X1 X2 X0
               grind)
            | exact superpose b4e349065 b4e29
            | (have j1 := b4e349065 X0 X2 X2
               grind)
            | exact resolve b4e29 b4e349065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e349065
          have b4e377871 : ∀ X0 X1 X2 : G, (k (σ (k (M.op X1 X2) (k X1 X2))) X0) = X0 ∨ y = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e377860 X0 X1 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e377860
            | (have j0 := b4e377860 X0 X1 X2
               grind)
            | exact resolve b4e377860 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e377860
          have b4e378678 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (σ (k (M.op X1 X2) (k X1 X2)))) X0) ∨ y = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29 X0 (σ (k (M.op X1 X2) (k X1 X2)))
               have i₂ := b4e377871 (τ X0) X1 X2
               grind)
            | exact superpose b4e377871 b4e29
            | (have j1 := b4e377871 X0 X1 X2
               grind)
            | exact resolve b4e29 b4e377871
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e377871
          have b4e378717 : ∀ X0 X1 X2 : G, (k (σ (σ (k (M.op X1 X2) (k X1 X2)))) X0) = X0 ∨ y = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e378678 X0 X1 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e378678
            | (have j0 := b4e378678 X0 X1 X2
               grind)
            | exact resolve b4e378678 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e378678
          have b4e384813 : ∀ X0 X1 : G, y = (M.op (M.op X1 y) (M.op (k X0 X1) (M.op X0 y))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e314770 X1 (M.op X0 y)
               have i₂ := b4e101 X0
               grind)
            | exact superpose b4e101 b4e314770
            | (have j0 := b4e314770 (M.op (M.op X1 y) (M.op (k X0 X1) (M.op X0 y))) X1
               grind)
            | exact resolve b4e314770 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e314770
          have b4e395120 : ∀ X0 : G, y = (M.op (σ (k (M.op (M.op X0 (τ x)) y) X0)) x) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e272779 (σ (k (M.op (M.op X0 (τ x)) y) X0))
               have i₂ := b4e317198 X0 x
               grind)
            | exact superpose b4e317198 b4e272779
            | (have j1 := b4e317198 (M.op (σ (k (M.op (M.op X0 (τ x)) y) X0)) x) x
               grind)
            | exact resolve b4e272779 b4e317198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e317198
          have b4e401079 : ∀ X0 X1 : G, y = (σ (σ (k (M.op X0 X1) (k X0 X1)))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e42076 (σ (σ (k (M.op X0 X1) (k X0 X1))))
               have i₂ := b4e378717 y X0 X1
               grind)
            | exact superpose b4e378717 b4e42076
            | (have j1 := b4e378717 X0 X1 (σ (σ (k (M.op X0 X1) (k X0 X1))))
               grind)
            | exact resolve b4e42076 b4e378717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e378717
          have b4e401297 : ∀ X0 X1 : G, y = (σ (σ (k X0 (k (M.op (M.op X1 X0) y) X1)))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e401079 (M.op (M.op X1 X0) y) X1
               have i₂ := b4e9440 X1 X0
               grind)
            | exact superpose b4e9440 b4e401079
            | (have j0 := b4e401079 X0 (σ (σ (k X0 (k (M.op (M.op X1 X0) y) X1))))
               grind)
            | exact resolve b4e401079 b4e9440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e401079
          have b4e402539 : ∀ X0 X1 : G, y ≠ y ∨ y = (M.op X0 (M.op (M.op (k X1 X0) (M.op X1 y)) y)) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e26999 X0 (M.op (k X1 X0) (M.op X1 y))
               have i₂ := b4e384813 X1 X0
               grind)
            | exact superpose b4e384813 b4e26999
            | (have j0 := b4e26999 X0 (M.op (k X1 X0) (M.op X1 y))
               have j1 := b4e384813 X0 (M.op X0 (M.op (M.op (k X1 X0) (M.op X1 y)) y))
               grind)
            | (have r₁ := b4e26999 X1 (M.op (k X0 X1) (M.op X0 y))
               have r₂ := b4e384813 X0 X1
               grind)
            | (have r₁ := b4e26999 X0 X1
               have r₂ := b4e384813 X0 (M.op (M.op X0 y) X1)
               grind)
            | exact resolve b4e26999 b4e384813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26999 b4e384813
          have b4e402552 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op (k X1 X0) (M.op X1 y)) y)) ∨ y = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e402539 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e402539
          have b4e402566 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op (k X1 X0) y) X1)) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e402552 X0 X1
               have i₂ := b4e8643 (k X1 X0) X1
               grind)
            | exact superpose b4e8643 b4e402552
            | (have j0 := b4e402552 (M.op X0 (M.op (M.op (k X1 X0) y) X1)) X1
               grind)
            | exact resolve b4e402552 b4e8643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e402552
          have b4e402733 : ∀ X0 X1 : G, y ≠ y ∨ y = (k (M.op (M.op (k X1 X0) y) X1) X0) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e355 (M.op (M.op (k X1 X0) y) X1) X0
               have i₂ := b4e402566 X0 X1
               grind)
            | exact superpose b4e402566 b4e355
            | (have j0 := b4e355 (M.op (M.op (k X1 X0) y) X1) X0
               have j1 := b4e402566 (k (M.op (M.op (k X1 X0) y) X1) X0) X1
               grind)
            | (have r₁ := b4e355 (M.op (M.op (k X1 X0) y) X1) X0
               have r₂ := b4e402566 X0 X1
               grind)
            | (have r₁ := b4e355 X0 X1
               have r₂ := b4e402566 (M.op X1 X0) X1
               grind)
            | exact resolve b4e355 b4e402566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e355 b4e402566
          have b4e402742 : ∀ X0 X1 : G, y = (k (M.op (M.op (k X1 X0) y) X1) X0) ∨ y = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e402733 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e402733
          have b4e403005 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k X0 X1) y) X0) X1) ∨ y = (M.op X1 y) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e305220 (M.op (M.op (k X0 X1) y) X0) X1
               have i₂ := b4e402742 X1 X0
               grind)
            | exact superpose b4e402742 b4e305220
            | (have j0 := b4e305220 X0 X1
               have j1 := b4e402742 (M.op (M.op (M.op (k X0 X1) y) X0) X1) X1
               grind)
            | exact resolve b4e305220 b4e402742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e305220 b4e402742
          have b4e403112 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k X0 X1) y) X0) X1) ∨ y = (M.op X1 y) := by
            intro X0 X1
            first
            | (have j0 := b4e403005 X0 X1
               have j1 := b4e13880 X1
               grind)
            | (have r₁ := b4e403005 X0 X1
               have r₂ := b4e13880 (M.op (M.op (M.op (k X0 X1) y) X0) X1)
               grind)
            | (have r₁ := b4e403005 X0 X1
               have r₂ := b4e13880 (M.op X1 y)
               grind)
            | (have r₁ := b4e403005 X0 X0
               have r₂ := b4e13880 X0
               grind)
            | exact resolve b4e403005 b4e13880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13880 b4e403005
          have b4e407338 : ∀ X0 X1 : G, (M.op (k X0 (σ X1)) y) = (M.op (σ (M.op (τ X0) X1)) y) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e314476 (τ X0) X1
               have i₂ := b4e28 X0 X1
               grind)
            | exact superpose b4e28 b4e314476
            | (have j0 := b4e314476 X0 X1
               grind)
            | exact resolve b4e314476 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e314476
          have b4e417111 : ∀ X0 : G, x = (M.op (M.op y y) (σ (k (M.op (M.op X0 (τ x)) y) X0))) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e9440 (σ (k (M.op (M.op X0 (τ x)) y) X0)) x
               have i₂ := b4e395120 X0
               grind)
            | exact superpose b4e395120 b4e9440
            | (have j1 := b4e395120 X0
               grind)
            | exact resolve b4e9440 b4e395120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e395120
          have b4e417121 : ∀ X0 : G, x = (M.op y (σ (k (M.op (M.op X0 (τ x)) y) X0))) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e417111 X0
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e417111
            | (have j0 := b4e417111 X0
               grind)
            | exact resolve b4e417111 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e417111
          have b4e417138 : ∀ X0 : G, x = (σ (k (M.op (M.op X0 (τ x)) y) X0)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e417121 X0
               have i₂ := b4e131 (σ (k (M.op (M.op X0 (τ x)) y) X0))
               grind)
            | exact superpose b4e131 b4e417121
            | (have j0 := b4e417121 X0
               grind)
            | exact resolve b4e417121 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e417121
          have b4e417194 : ∀ X0 : G, x = (k (σ (M.op (M.op (τ X0) (τ x)) y)) X0) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e29 X0 (M.op (M.op (τ X0) (τ x)) y)
               have i₂ := b4e417138 (τ X0)
               grind)
            | exact superpose b4e417138 b4e29
            | (have j1 := b4e417138 (τ X0)
               grind)
            | exact resolve b4e29 b4e417138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e417138
          have b4e427399 : ∀ X0 X1 : G, y = (σ (k X0 (σ (k (M.op (M.op X1 (τ X0)) y) X1)))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e401297 (τ X0) X1
               have i₂ := b4e28 X0 (k (M.op (M.op X1 (τ X0)) y) X1)
               grind)
            | exact superpose b4e28 b4e401297
            | (have j0 := b4e401297 X0 (σ (k X0 (σ (k (M.op (M.op X1 (τ X0)) y) X1))))
               grind)
            | exact resolve b4e401297 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e401297
          have b4e435403 : ∀ X0 X1 : G, (M.op (M.op y y) (M.op (M.op (k X0 X1) y) X0)) = X1 ∨ y = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e9440 (M.op (M.op (k X0 X1) y) X0) X1
               have i₂ := b4e403112 X0 X1
               grind)
            | exact superpose b4e403112 b4e9440
            | (have j1 := b4e403112 X0 X1
               grind)
            | exact resolve b4e9440 b4e403112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e403112
          have b4e435459 : ∀ X0 X1 : G, (M.op y (M.op (M.op (k X0 X1) y) X0)) = X1 ∨ y = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e435403 X0 X1
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e435403
            | (have j0 := b4e435403 X0 X1
               grind)
            | exact resolve b4e435403 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e435403
          have b4e435491 : ∀ X0 X1 : G, (M.op (M.op (k X0 X1) y) X0) = X1 ∨ y = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e435459 X0 X1
               have i₂ := b4e131 (M.op (M.op (k X0 X1) y) X0)
               grind)
            | exact superpose b4e131 b4e435459
            | (have j0 := b4e435459 X0 X1
               grind)
            | exact resolve b4e435459 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e435459
          have b4e435633 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (k X1 X0) y)) = X1 ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e9440 (M.op (k X1 X0) y) X1
               have i₂ := b4e435491 X1 X0
               grind)
            | exact superpose b4e435491 b4e9440
            | (have j1 := b4e435491 X0 X0
               grind)
            | exact resolve b4e9440 b4e435491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e435491
          have b4e435790 : ∀ X0 X1 : G, (M.op (M.op X0 (k X1 X0)) y) = X1 ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e435633 X0 X1
               have i₂ := b4e9034 (k X1 X0) X0
               grind)
            | exact superpose b4e9034 b4e435633
            | (have j0 := b4e435633 X0 X1
               grind)
            | exact resolve b4e435633 b4e9034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e435633
          have b4e436776 : ∀ X0 X1 : G, (M.op X1 (M.op (k X0 (M.op X1 y)) y)) = X0 ∨ y = (M.op (M.op X1 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e8667 (k X0 (M.op X1 y)) X1
               have i₂ := b4e435790 (M.op X1 y) X0
               grind)
            | exact superpose b4e435790 b4e8667
            | (have j1 := b4e435790 (M.op X1 y) X1
               grind)
            | exact resolve b4e8667 b4e435790
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8667 b4e435790
          have b4e436864 : ∀ X0 X1 : G, (M.op X1 (M.op (k X0 (M.op X1 y)) y)) = X0 ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e436776 X0 X1
               have i₂ := b4e101 X1
               grind)
            | exact superpose b4e101 b4e436776
            | (have j0 := b4e436776 X0 X1
               grind)
            | exact resolve b4e436776 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e436776
          have b4e437530 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (k X0 (M.op X1 y)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e102 X1 (k X0 (M.op X1 y))
               have i₂ := b4e436864 X0 X1
               grind)
            | exact superpose b4e436864 b4e102
            | (have j1 := b4e436864 X0 X1
               grind)
            | exact resolve b4e102 b4e436864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102 b4e436864
          have b4e437625 : ∀ X0 X1 X2 : G, y = (M.op X2 (k X0 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ y = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e437530 X0 (M.op X0 (k X1 X0))
               have i₂ := b4e309490 X0 X1
               grind)
            | exact superpose b4e309490 b4e437530
            | (have j0 := b4e437530 X0 (M.op X2 (k X0 X2))
               have j1 := b4e309490 (M.op X2 (k X0 X2)) X1
               grind)
            | exact resolve b4e437530 b4e309490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e309490 b4e437530
          have b4e502880 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k X0 (σ X1)) y) y) (σ (M.op (τ X0) X1))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e9440 (σ (M.op (τ X0) X1)) y
               have i₂ := b4e407338 X0 X1
               grind)
            | exact superpose b4e407338 b4e9440
            | (have j1 := b4e407338 X0 (M.op (M.op (M.op (k X0 (σ X1)) y) y) (σ (M.op (τ X0) X1)))
               grind)
            | exact resolve b4e9440 b4e407338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e407338
          have b4e502881 : ∀ X0 X1 : G, y = (M.op (k X0 (σ X1)) (σ (M.op (τ X0) X1))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e502880 X0 X1
               have i₂ := b4e101 (k X0 (σ X1))
               grind)
            | exact superpose b4e101 b4e502880
            | (have j0 := b4e502880 X0 (M.op (k X0 (σ X1)) (σ (M.op (τ X0) X1)))
               grind)
            | exact resolve b4e502880 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e502880
          have b4e528221 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op (M.op y y) X0) ∨ (M.op X2 X1) = (k X2 X1) ∨ y = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e9440 X0 (k X1 X0)
               have i₂ := b4e437625 X1 X2 X0
               grind)
            | exact superpose b4e437625 b4e9440
            | (have j1 := b4e437625 X1 X2 X0
               grind)
            | exact resolve b4e9440 b4e437625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e437625
          have b4e528241 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op y X0) ∨ (M.op X2 X1) = (k X2 X1) ∨ y = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e528221 X0 X1 X2
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e528221
            | (have j0 := b4e528221 X0 X1 X2
               grind)
            | exact resolve b4e528221 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528221
          have b4e528253 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (k X1 X0) = X0 ∨ y = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e528241 X0 X1 X2
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e528241
            | (have j0 := b4e528241 X0 X1 X2
               grind)
            | exact resolve b4e528241 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528241
          have b4e528330 : ∀ X0 X1 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op X1 X0) = (k X1 X0) ∨ y = (σ x) := by
            intro X0 X1
            first
            | (have i₁ := b4e286956 X0
               have i₂ := b4e528253 (σ x) X0 X1
               grind)
            | exact superpose b4e528253 b4e286956
            | (have j1 := b4e528253 (σ x) X0 X1
               grind)
            | exact resolve b4e286956 b4e528253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528253
          have b4e528348 : ∀ X0 X1 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e528330 X0 X1
               grind)
            | (have r₁ := b4e528330 X0 X1
               have r₂ := b4e402
               grind)
            | exact resolve b4e528330 b4e402
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528330
          have b4e528821 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (τ X0) x) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e286311 X0
               have i₂ := b4e528348 X0 X1
               grind)
            | exact superpose b4e528348 b4e286311
            | (have j1 := b4e528348 X0 X1
               grind)
            | exact resolve b4e286311 b4e528348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528348
          have b4e528896 : ∀ X0 X1 : G, x = (M.op (τ X0) x) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e528821 X0 X1
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e528821
            | (have j0 := b4e528821 X0 X1
               grind)
            | exact resolve b4e528821 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528821
          have b4e528950 : ∀ X0 X1 : G, (M.op x x) = (M.op (τ X0) y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 (τ X0) x
               have i₂ := b4e528896 X0 X1
               grind)
            | exact superpose b4e528896 b4e40
            | (have j1 := b4e528896 X0 X1
               grind)
            | exact resolve b4e40 b4e528896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528896
          have b4e529085 : ∀ X0 X1 : G, y = (M.op (τ X0) y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e528950 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e528950
            | (have j0 := b4e528950 X0 X1
               grind)
            | exact resolve b4e528950 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528950
          have b4e529200 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (M.op (M.op y (M.op X1 y)) y) ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e517 X1 (τ X0)
               have i₂ := b4e529085 X0 X2
               grind)
            | exact superpose b4e529085 b4e517
            | (have j1 := b4e529085 X0 X2
               grind)
            | exact resolve b4e517 b4e529085
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e517
          have b4e529206 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) y) = (M.op (M.op X0 (τ X1)) y) ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e9034 (τ X1) X0
               have i₂ := b4e529085 X1 X2
               grind)
            | exact superpose b4e529085 b4e9034
            | (have j1 := b4e529085 X1 X2
               grind)
            | exact resolve b4e9034 b4e529085
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e529210 : ∀ X0 X1 : G, y ≠ y ∨ (τ X0) = y ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13710 (τ X0)
               have i₂ := b4e529085 X0 X1
               grind)
            | exact superpose b4e529085 b4e13710
            | (have j0 := b4e13710 (τ X0)
               have j1 := b4e529085 X0 X1
               grind)
            | (have r₁ := b4e13710 (τ X0)
               have r₂ := b4e529085 X0 X1
               grind)
            | exact resolve b4e13710 b4e529085
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529085
          have b4e529283 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = y := by
            intro X0 X1
            first
            | (have j0 := b4e529210 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529210
          have b4e529334 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (τ X1)) y) = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e529206 X0 X1 X2
               have i₂ := b4e101 X0
               grind)
            | exact superpose b4e101 b4e529206
            | (have j0 := b4e529206 X0 X1 X2
               grind)
            | exact resolve b4e529206 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529206
          have b4e529339 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (M.op (M.op y y) X1) ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e529200 X0 X1 X2
               have i₂ := b4e8643 y X1
               grind)
            | exact superpose b4e8643 b4e529200
            | (have j0 := b4e529200 X0 X1 X2
               grind)
            | exact resolve b4e529200 b4e8643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8643 b4e529200
          have b4e529386 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (M.op y X1) ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e529339 X0 X1 X2
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e529339
            | (have j0 := b4e529339 X0 X1 X2
               grind)
            | exact resolve b4e529339 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529339
          have b4e529397 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e529386 X0 X1 X2
               have i₂ := b4e131 X1
               grind)
            | exact superpose b4e131 b4e529386
            | (have j0 := b4e529386 X0 X1 X2
               grind)
            | exact resolve b4e529386 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529386
          have b4e529774 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ y = (τ (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e529283 (σ X1) (σ X0)
               grind)
            | exact superpose b4e529283 b4e19
            | (have j1 := b4e529283 (σ X1) X1
               grind)
            | exact resolve b4e19 b4e529283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529283
          have b4e529979 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e529774 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e529774
            | (have j0 := b4e529774 X0 X1
               grind)
            | exact resolve b4e529774 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529774
          have b4e530444 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (τ (τ X0)) x) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e286311 (τ X0)
               have i₂ := b4e529397 X0 (σ x) X1
               grind)
            | exact superpose b4e529397 b4e286311
            | (have j1 := b4e529397 X0 X1 X1
               grind)
            | exact resolve b4e286311 b4e529397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e286311 b4e529397
          have b4e530635 : ∀ X0 X1 : G, x = (M.op (τ (τ X0)) x) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e530444 X0 X1
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e530444
            | (have j0 := b4e530444 X0 X1
               grind)
            | exact resolve b4e530444 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e530444
          have b4e530723 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e529979 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e529979
            | (have j0 := b4e529979 X0 X1
               grind)
            | exact resolve b4e529979 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529979
          have b4e530920 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e530723 X0 X1
               have i₂ := b4e28 X0 X1
               grind)
            | exact superpose b4e28 b4e530723
            | (have j0 := b4e530723 X0 X1
               grind)
            | exact resolve b4e530723 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e530723
          have b4e531090 : ∀ X0 X1 : G, y = (M.op (M.op X0 (σ X1)) (σ (M.op (τ X0) X1))) ∨ y = X1 ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e502881 X0 X1
               have i₂ := b4e530920 X0 X1
               grind)
            | exact superpose b4e530920 b4e502881
            | (have j0 := b4e502881 X0 (M.op (M.op X0 (σ X1)) (σ (M.op (τ X0) X1)))
               have j1 := b4e530920 X0 (M.op (M.op X0 (σ X1)) (σ (M.op (τ X0) X1)))
               grind)
            | exact resolve b4e502881 b4e530920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e502881 b4e530920
          have b4e531173 : ∀ X0 X1 : G, y = (M.op (M.op X0 (σ X1)) (σ (M.op (τ X0) X1))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e531090 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e531090
          have b4e532814 : ∀ X0 X1 : G, (M.op x x) = (M.op (τ (τ X0)) y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 (τ (τ X0)) x
               have i₂ := b4e530635 X0 X1
               grind)
            | exact superpose b4e530635 b4e40
            | (have j1 := b4e530635 X0 X1
               grind)
            | exact resolve b4e40 b4e530635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e530635
          have b4e532893 : ∀ X0 X1 : G, y = (M.op (τ (τ X0)) y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e532814 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e532814
            | (have j0 := b4e532814 X0 X1
               grind)
            | exact resolve b4e532814 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e532814
          have b4e533216 : ∀ X0 X1 : G, y ≠ y ∨ y = (τ (τ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13710 (τ (τ X0))
               have i₂ := b4e532893 X0 X1
               grind)
            | exact superpose b4e532893 b4e13710
            | (have j0 := b4e13710 (τ (τ X0))
               have j1 := b4e532893 X0 X1
               grind)
            | (have r₁ := b4e13710 (τ (τ X0))
               have r₂ := b4e532893 X0 X1
               grind)
            | exact resolve b4e13710 b4e532893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13710 b4e532893
          have b4e533267 : ∀ X0 X1 : G, y = (τ (τ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e533216 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533216
          have b4e533441 : ∀ X0 X1 X2 : G, (k y (τ X1)) = (τ (k (τ X0) X1)) ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e4353 X1 (τ X0)
               have i₂ := b4e533267 X0 X2
               grind)
            | exact superpose b4e533267 b4e4353
            | (have j1 := b4e533267 X0 X2
               grind)
            | exact resolve b4e4353 b4e533267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533267
          have b4e533797 : ∀ X0 X1 X2 : G, (τ X1) = (τ (k (τ X0) X1)) ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e533441 X0 X1 X2
               have i₂ := b4e11552 (τ X1)
               grind)
            | exact superpose b4e11552 b4e533441
            | (have j0 := b4e533441 X0 X1 X2
               grind)
            | exact resolve b4e533441 b4e11552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11552 b4e533441
          have b4e536584 : ∀ X0 X1 X2 : G, y = (σ (k X1 (σ (k X0 X0)))) ∨ y = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e427399 X1 X0
               have i₂ := b4e529334 X0 X1 X2
               grind)
            | exact superpose b4e529334 b4e427399
            | (have j0 := b4e427399 X0 (σ (k X1 (σ (k X0 X0))))
               have j1 := b4e529334 X0 X1 X2
               grind)
            | exact resolve b4e427399 b4e529334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e427399 b4e529334
          have b4e536730 : ∀ X0 X1 X2 : G, y = (σ (k X1 (σ (M.op X0 X0)))) ∨ y = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e536584 X0 X1 X2
               have i₂ := b4e46 X0
               grind)
            | exact superpose b4e46 b4e536584
            | (have j0 := b4e536584 (σ (k X1 (σ (M.op X0 X0)))) X1 X2
               grind)
            | exact resolve b4e536584 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e536584
          have b4e536778 : ∀ X0 X1 X2 : G, y = (σ (k X1 (σ y))) ∨ y = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e536730 X0 X1 X2
               have i₂ := b4e188 X0
               grind)
            | exact superpose b4e188 b4e536730
            | (have j0 := b4e536730 (σ (k X1 (σ y))) X1 X2
               grind)
            | exact resolve b4e536730 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e536730
          have b4e536801 : ∀ X0 X1 X2 : G, y = (σ (k X1 y)) ∨ y = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e536778 X0 X1 X2
               have i₂ := b4e364
               grind)
            | exact superpose b4e364 b4e536778
            | (have j0 := b4e536778 (σ (k X1 y)) X1 X2
               grind)
            | exact resolve b4e536778 b4e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e364 b4e536778
          have b4e536813 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ y = X0 ∨ (σ X1) = y := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e536801 X0 X1 X2
               have i₂ := b4e42076 X1
               grind)
            | exact superpose b4e42076 b4e536801
            | (have j0 := b4e536801 X0 X1 X2
               grind)
            | exact resolve b4e536801 b4e42076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e536801
          have b4e537541 : ∀ X0 X1 : G, y ≠ y ∨ (k X0 X1) = (M.op X0 X1) ∨ (σ X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b4e295072
               have i₂ := b4e536813 (M.op (σ x) y) X1 X0
               grind)
            | exact superpose b4e536813 b4e295072
            | (have j1 := b4e536813 (σ X1) X1 X0
               grind)
            | (have r₁ := b4e295072
               have r₂ := b4e536813 (M.op (σ x) y) X1 x
               grind)
            | exact resolve b4e295072 b4e536813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e295072 b4e536813
          have b4e538396 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X1) = y := by
            intro X0 X1
            first
            | (have j0 := b4e537541 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e537541
          have b4e538864 : ∀ X0 : G, x = (M.op (τ (M.op (σ (M.op X0 x)) y)) X0) ∨ (σ X0) = y ∨ (σ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e287933 X0
               have i₂ := b4e538396 (τ (M.op (σ (M.op X0 x)) y)) X0
               grind)
            | exact superpose b4e538396 b4e287933
            | (have j0 := b4e287933 X0
               have j1 := b4e538396 X0 X0
               grind)
            | exact resolve b4e287933 b4e538396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287933
          have b4e538877 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ y = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e4353 X1 X0
               have i₂ := b4e538396 (τ X0) (τ X1)
               grind)
            | exact superpose b4e538396 b4e4353
            | (have j1 := b4e538396 X0 (τ X1)
               grind)
            | exact resolve b4e4353 b4e538396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4353 b4e538396
          have b4e539031 : ∀ X0 : G, x = (M.op (τ (M.op (σ (M.op X0 x)) y)) X0) ∨ (σ X0) = y := by
            intro X0
            first
            | (have j0 := b4e538864 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e538864
          have b4e539071 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e538877 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e538877
            | (have j0 := b4e538877 X0 X1
               grind)
            | exact resolve b4e538877 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e538877
          have b4e539505 : ∀ X0 : G, x = (k (σ (M.op (τ (k X0 x)) y)) X0) ∨ (τ X0) = y ∨ x = y := by
            intro X0
            first
            | (have i₁ := b4e417194 X0
               have i₂ := b4e539071 X0 x
               grind)
            | exact superpose b4e539071 b4e417194
            | (have j0 := b4e417194 X0
               have j1 := b4e539071 X0 (τ X0)
               grind)
            | exact resolve b4e417194 b4e539071
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e417194
          have b4e539550 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op (τ (k X0 X1)) y) (τ X0)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e9440 (τ X0) (τ X1)
               have i₂ := b4e539071 X0 X1
               grind)
            | exact superpose b4e539071 b4e9440
            | (have j1 := b4e539071 X0 X1
               grind)
            | exact resolve b4e9440 b4e539071
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e539071
          have b4e539598 : ∀ X0 : G, x = (k (σ (M.op (τ (k X0 x)) y)) X0) ∨ (τ X0) = y := by
            intro X0
            first
            | (have j0 := b4e539505 X0
               grind)
            | (have r₁ := b4e539505 X0
               have r₂ := b4e182
               grind)
            | exact resolve b4e539505 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e539505
          have b4e539656 : ∀ X0 : G, x = (k (σ (M.op (τ (M.op X0 x)) y)) X0) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e539598 X0
               have i₂ := b4e272779 X0
               grind)
            | exact superpose b4e272779 b4e539598
            | (have j0 := b4e539598 X0
               grind)
            | exact resolve b4e539598 b4e272779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e539598
          have b4e553970 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op (M.op y y) (M.op X0 (σ X1))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e9440 (M.op X0 (σ X1)) (σ (M.op (τ X0) X1))
               have i₂ := b4e531173 X0 X1
               grind)
            | exact superpose b4e531173 b4e9440
            | (have j1 := b4e531173 X0 X1
               grind)
            | exact resolve b4e9440 b4e531173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e531173
          have b4e553973 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op y (M.op X0 (σ X1))) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e553970 X0 X1
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e553970
            | (have j0 := b4e553970 X0 X1
               grind)
            | exact resolve b4e553970 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e553970
          have b4e553988 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e553973 X0 X1
               have i₂ := b4e131 (M.op X0 (σ X1))
               grind)
            | exact superpose b4e131 b4e553973
            | (have j0 := b4e553973 X0 X1
               grind)
            | exact resolve b4e553973 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e553973
          have b4e560257 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (τ X1) X0) ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e15 (k (τ X1) X0)
               have i₂ := b4e533797 X1 X0 X2
               grind)
            | exact superpose b4e533797 b4e15
            | (have j1 := b4e533797 X1 X1 X2
               grind)
            | exact resolve b4e15 b4e533797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533797
          have b4e560283 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e560257 X0 X1 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e560257
            | (have j0 := b4e560257 X0 X1 X2
               grind)
            | exact resolve b4e560257 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e560257
          have b4e560413 : ∀ X0 X1 X2 : G, (k (τ X0) y) = (τ (k X0 (k X1 y))) ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e6473 X1 X0
               have i₂ := b4e560283 y X1 X2
               grind)
            | exact superpose b4e560283 b4e6473
            | (have j1 := b4e560283 X0 X1 X2
               grind)
            | exact resolve b4e6473 b4e560283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6473 b4e560283
          have b4e560541 : ∀ X0 X1 X2 : G, (k (τ X0) y) = (τ (k X0 X1)) ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e560413 X0 X1 X2
               have i₂ := b4e42076 X1
               grind)
            | exact superpose b4e42076 b4e560413
            | (have j0 := b4e560413 X0 X1 X2
               grind)
            | exact resolve b4e560413 b4e42076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e560413
          have b4e560576 : ∀ X0 X1 X2 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e560541 X0 X1 X2
               have i₂ := b4e42076 (τ X0)
               grind)
            | exact superpose b4e42076 b4e560541
            | (have j0 := b4e560541 X0 X1 X2
               grind)
            | exact resolve b4e560541 b4e42076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42076 b4e560541
          have b4e562022 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e15 (k X0 X1)
               have i₂ := b4e560576 X0 X1 X2
               grind)
            | exact superpose b4e560576 b4e15
            | (have j1 := b4e560576 X0 X1 X2
               grind)
            | exact resolve b4e15 b4e560576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e560576
          have b4e562066 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e562022 X0 X1 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e562022
            | (have j0 := b4e562022 X0 X1 X2
               grind)
            | exact resolve b4e562022 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e562022
          have b4e562444 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e562066 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e562066
          have b4e562497 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X0 y) X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e562444 X1 (M.op (M.op X0 y) X1)
               have i₂ := b4e34 X1 X0
               grind)
            | exact superpose b4e34 b4e562444
            | (have j0 := b4e562444 X1 (M.op (M.op X0 y) X1)
               grind)
            | (have r₁ := b4e562444 X1 (M.op (M.op X1 y) X1)
               have r₂ := b4e34 X1 X1
               grind)
            | exact resolve b4e562444 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e562444
          have b4e562578 : ∀ X0 : G, (k X0 (M.op (M.op X0 y) X0)) = X0 := by
            intro X0
            first
            | (have j0 := b4e562497 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e562497
          have b4e562722 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ (M.op (M.op x y) x)) := by
            first
            | (have i₁ := b4e320883 (M.op x y)
               have i₂ := b4e562578 x
               grind)
            | exact superpose b4e562578 b4e320883
            | (have j0 := b4e320883 (M.op x y)
               grind)
            | exact resolve b4e320883 b4e562578
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e320883 b4e562578
          have b4e562750 : y = (σ (M.op (M.op x y) x)) := by
            first
            | (have r₁ := b4e562722
               have r₂ := b4e405
               grind)
            | exact resolve b4e562722 b4e405
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e562722
          have b4e562835 : (σ x) = (M.op (M.op (σ (M.op x y)) y) y) := by
            first
            | (have i₁ := b4e289161 x
               have i₂ := b4e562750
               grind)
            | exact superpose b4e562750 b4e289161
            | exact resolve b4e289161 b4e562750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e289161
          have b4e562859 : x = (M.op (τ (M.op y y)) (M.op x y)) ∨ y = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e539031 (M.op x y)
               have i₂ := b4e562750
               grind)
            | exact superpose b4e562750 b4e539031
            | (have j0 := b4e539031 (M.op x y)
               grind)
            | exact resolve b4e539031 b4e562750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e539031 b4e562750
          have b4e563129 : x = (M.op (τ y) (M.op x y)) ∨ y = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e562859
               have i₂ := b4e188 y
               grind)
            | exact superpose b4e188 b4e562859
            | exact resolve b4e562859 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e188 b4e562859
          have b4e563149 : (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b4e562835
               have i₂ := b4e101 (σ (M.op x y))
               grind)
            | exact superpose b4e101 b4e562835
            | exact resolve b4e562835 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e562835
          have b4e563198 : x = (M.op y (M.op x y)) ∨ y = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e563129
               have i₂ := b4e409
               grind)
            | exact superpose b4e409 b4e563129
            | exact resolve b4e563129 b4e409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e409 b4e563129
          have b4e563236 : x = (M.op x y) ∨ y = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e563198
               have i₂ := b4e40 x y
               grind)
            | exact superpose b4e40 b4e563198
            | exact resolve b4e563198 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e563198
          have b4e563252 : y = (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e563236
               have i₂ := b4e563149
               grind)
            | exact superpose b4e563149 b4e563236
            | exact resolve b4e563236 b4e563149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e563149 b4e563236
          have b4e563264 : x = (M.op x y) := by
            first
            | (have r₁ := b4e563252
               have r₂ := b4e402
               grind)
            | exact resolve b4e563252 b4e402
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e402 b4e563252
          have b4e563276 : (σ x) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e405
               have i₂ := b4e563264
               grind)
            | exact superpose b4e563264 b4e405
            | exact resolve b4e405 b4e563264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e563356 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) x) := by
            intro X0
            first
            | (have i₁ := b4e94 x X0
               have i₂ := b4e563264
               grind)
            | exact superpose b4e563264 b4e94
            | exact resolve b4e94 b4e563264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e563383 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b4e9034 x X0
               have i₂ := b4e563264
               grind)
            | exact superpose b4e563264 b4e9034
            | exact resolve b4e9034 b4e563264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e604984 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op (τ (k (σ X0) X1)) y) X0) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e539550 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e539550
            | (have j0 := b4e539550 X0 X1
               grind)
            | exact resolve b4e539550 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e539550
          have b4e605013 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op (k X0 (τ X1)) y) X0) ∨ y = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e604984 X0 X1
               have i₂ := b4e124 X0 X1
               grind)
            | exact superpose b4e124 b4e604984
            | (have j0 := b4e604984 X0 X1
               grind)
            | exact resolve b4e604984 b4e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124 b4e604984
          have b4e605113 : ∀ X0 X1 : G, (M.op (M.op (τ X0) y) (M.op (k X1 (τ X0)) y)) = X1 ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e9440 (M.op (k X1 (τ X0)) y) X1
               have i₂ := b4e605013 X1 X0
               grind)
            | exact superpose b4e605013 b4e9440
            | (have j1 := b4e605013 X0 X0
               grind)
            | exact resolve b4e9440 b4e605013
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e605013
          have b4e605197 : ∀ X0 X1 : G, (M.op (M.op (τ X0) (k X1 (τ X0))) y) = X1 ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e605113 X0 X1
               have i₂ := b4e9034 (k X1 (τ X0)) (τ X0)
               grind)
            | exact superpose b4e9034 b4e605113
            | (have j0 := b4e605113 X0 X1
               grind)
            | exact resolve b4e605113 b4e9034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9034 b4e605113
          have b4e609376 : x = (M.op (σ (M.op (τ (M.op (σ x) x)) y)) (σ x)) ∨ y = (τ (σ x)) := by
            first
            | (have i₁ := b4e286956 (σ (M.op (τ (M.op (σ x) x)) y))
               have i₂ := b4e539656 (σ x)
               grind)
            | exact superpose b4e539656 b4e286956
            | (have j1 := b4e539656 (σ x)
               grind)
            | exact resolve b4e286956 b4e539656
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e539656
          have b4e609385 : x = (σ (M.op (M.op (τ (M.op (σ x) x)) y) x)) ∨ y = (τ (σ x)) := by
            first
            | (have i₁ := b4e609376
               have i₂ := b4e286924 (M.op (τ (M.op (σ x) x)) y)
               grind)
            | exact superpose b4e286924 b4e609376
            | exact resolve b4e609376 b4e286924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e286924 b4e609376
          have b4e609395 : x = (σ (M.op (M.op (τ (M.op (σ x) x)) x) y)) ∨ y = (τ (σ x)) := by
            first
            | (have i₁ := b4e609385
               have i₂ := b4e563383 (τ (M.op (σ x) x))
               grind)
            | exact superpose b4e563383 b4e609385
            | exact resolve b4e609385 b4e563383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e563383 b4e609385
          have b4e609405 : x = (σ (M.op (M.op (k x (τ x)) x) y)) ∨ y = (τ (σ x)) := by
            first
            | (have i₁ := b4e609395
               have i₂ := b4e273129 x
               grind)
            | exact superpose b4e273129 b4e609395
            | exact resolve b4e609395 b4e273129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e273129 b4e609395
          have b4e609412 : x = y ∨ x = (σ (M.op (M.op (k x (τ x)) x) y)) := by
            first
            | (have i₁ := b4e609405
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e609405
            | exact resolve b4e609405 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e609405
          have b4e609418 : x = (σ (M.op (M.op (k x (τ x)) x) y)) := by
            first
            | (have r₁ := b4e609412
               have r₂ := b4e182
               grind)
            | exact resolve b4e609412 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e609412
          have b4e609475 : (τ x) = (M.op (M.op (k x (τ x)) x) y) := by
            first
            | (have i₁ := b4e14 (M.op (M.op (k x (τ x)) x) y)
               have i₂ := b4e609418
               grind)
            | exact superpose b4e609418 b4e14
            | exact resolve b4e14 b4e609418
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e609644 : x = (M.op (τ x) (k x (τ x))) := by
            first
            | (have i₁ := b4e9440 (k x (τ x)) x
               have i₂ := b4e609475
               grind)
            | exact superpose b4e609475 b4e9440
            | exact resolve b4e9440 b4e609475
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9440 b4e609475
          have b4e610089 : (σ x) = (M.op x (σ (k x (τ x)))) ∨ y = (k x (τ x)) := by
            first
            | (have i₁ := b4e553988 x (k x (τ x))
               have i₂ := b4e609644
               grind)
            | exact superpose b4e609644 b4e553988
            | (have j0 := b4e553988 x (k x (τ x))
               grind)
            | exact resolve b4e553988 b4e609644
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e553988 b4e609644
          have b4e610205 : (σ x) = (M.op x (k (σ x) x)) ∨ y = (k x (τ x)) := by
            first
            | (have i₁ := b4e610089
               have i₂ := b4e29 x x
               grind)
            | exact superpose b4e29 b4e610089
            | exact resolve b4e610089 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e610089
          have b4e610356 : (σ x) = (M.op x (M.op (σ x) x)) ∨ y = (k x (τ x)) := by
            first
            | (have i₁ := b4e610205
               have i₂ := b4e272779 (σ x)
               grind)
            | exact superpose b4e272779 b4e610205
            | exact resolve b4e610205 b4e272779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272779 b4e610205
          have b4e610430 : (σ x) = (M.op (σ x) y) ∨ y = (k x (τ x)) := by
            first
            | (have i₁ := b4e610356
               have i₂ := b4e40 (σ x) x
               grind)
            | exact superpose b4e40 b4e610356
            | exact resolve b4e610356 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e610356
          have b4e610468 : y = (k x (τ x)) := by
            first
            | (have r₁ := b4e610430
               have r₂ := b4e563276
               grind)
            | exact resolve b4e610430 b4e563276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e563276 b4e610430
          have b4e610515 : x = (σ (M.op (M.op y x) y)) := by
            first
            | (have i₁ := b4e609418
               have i₂ := b4e610468
               grind)
            | exact superpose b4e610468 b4e609418
            | exact resolve b4e609418 b4e610468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e609418
          have b4e610695 : x = (M.op (M.op (τ x) y) y) ∨ x = y := by
            first
            | (have i₁ := b4e605197 x x
               have i₂ := b4e610468
               grind)
            | exact superpose b4e610468 b4e605197
            | (have j0 := b4e605197 x x
               grind)
            | exact resolve b4e605197 b4e610468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e605197 b4e610468
          have b4e611978 : x = (M.op (M.op (τ x) y) y) := by
            first
            | (have r₁ := b4e610695
               have r₂ := b4e182
               grind)
            | exact resolve b4e610695 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e182 b4e610695
          have b4e612121 : x = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e610515
               have i₂ := b4e131 x
               grind)
            | exact superpose b4e131 b4e610515
            | exact resolve b4e610515 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131 b4e610515
          have b4e612460 : x = (τ x) := by
            first
            | (have i₁ := b4e611978
               have i₂ := b4e101 (τ x)
               grind)
            | exact superpose b4e101 b4e611978
            | exact resolve b4e611978 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101 b4e611978
          have b4e612561 : x = (σ x) := by
            first
            | (have i₁ := b4e612121
               have i₂ := b4e563264
               grind)
            | exact superpose b4e563264 b4e612121
            | exact resolve b4e612121 b4e563264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e563264 b4e612121
          have b4e613353 : (M.op (k x (σ (σ x))) (σ x)) = (σ (M.op (M.op x (σ x)) x)) := by
            first
            | (have i₁ := b4e288768 x
               have i₂ := b4e612460
               grind)
            | exact superpose b4e612460 b4e288768
            | exact resolve b4e288768 b4e612460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e288768 b4e612460
          have b4e613690 : (σ (M.op (σ x) y)) = (M.op (k x (σ (σ x))) (σ x)) := by
            first
            | (have i₁ := b4e613353
               have i₂ := b4e563356 (σ x)
               grind)
            | exact superpose b4e563356 b4e613353
            | exact resolve b4e613353 b4e563356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e613353
          have b4e613875 : (σ (M.op x y)) = (M.op (k x (σ x)) x) := by
            first
            | (have i₁ := b4e613690
               have i₂ := b4e612561
               grind)
            | exact superpose b4e612561 b4e613690
            | exact resolve b4e613690 b4e612561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e612561 b4e613690
          have b4e614041 : (σ (M.op x y)) = (M.op (M.op x (σ x)) x) := by
            first
            | (have i₁ := b4e613875
               have i₂ := b4e286956 x
               grind)
            | exact superpose b4e286956 b4e613875
            | exact resolve b4e613875 b4e286956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e286956 b4e613875
          have b4e614143 : (σ (M.op x y)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e614041
               have i₂ := b4e563356 (σ x)
               grind)
            | exact superpose b4e563356 b4e614041
            | exact resolve b4e614041 b4e563356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e563356 b4e614041
          have b4e614208 : False := by grind
          exact b4e614208
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X2)) X1)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b5e29 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 y) X1 (M.op X0 y)
               have i₂ := b5e29 (M.op X0 y) X0
               grind)
            | exact superpose b5e29 b5e13
            | exact resolve b5e13 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29 x X0
               have i₂ := b5e34 (M.op X0 y) x
               grind)
            | exact superpose b5e34 b5e29
            | exact resolve b5e29 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e94 : ∀ X0 : G, (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e34 (M.op X0 y) y
               have i₂ := b5e43 X0
               grind)
            | exact superpose b5e43 b5e34
            | exact resolve b5e34 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e120 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e34 y X0
               have i₂ := b5e94 X0
               grind)
            | exact superpose b5e94 b5e34
            | exact resolve b5e34 b5e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e129 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b5e120 X0
               have i₂ := b5e94 y
               grind)
            | exact superpose b5e94 b5e120
            | exact resolve b5e120 b5e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94 b5e120
          have b5e154 : ∀ X0 : G, y ≠ y ∨ y = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e16 X0 X0
               have i₂ := b5e129 X0
               grind)
            | exact superpose b5e129 b5e16
            | exact resolve b5e16 b5e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e157 : y ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e129 (σ x)
               grind)
            | exact superpose b5e129 b5e24
            | exact resolve b5e24 b5e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129
          have b5e162 : ∀ X0 : G, y = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e154 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e154
          have b5e451 : ∀ X0 : G, (σ y) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 (τ X0)
               have i₂ := b5e162 (τ X0)
               grind)
            | exact superpose b5e162 b5e27
            | exact resolve b5e27 b5e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e452 : ∀ X0 : G, (σ y) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e451 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e451
            | exact resolve b5e451 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e451
          have b5e456 : y = (σ y) := by
            first
            | (have i₁ := b5e452 x
               have i₂ := b5e162 x
               grind)
            | exact superpose b5e162 b5e452
            | exact resolve b5e452 b5e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e162 b5e452
          have b5e460 : False := by grind
          exact b5e460
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X2)) X1)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e30 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
             have i₂ := b6e12 X0 (M.op X0 (M.op X2 X2)) X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e48
        have b6e51 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e50
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e50
          | exact resolve b6e50 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e94 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e51
             grind)
          | exact superpose b6e51 b6e15
          | exact resolve b6e15 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e95 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e94
        have b6e96 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e95
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e95
          | exact resolve b6e95 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e98 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e96
             have i₂ := b6e49 x
             grind)
          | exact superpose b6e49 b6e96
          | exact resolve b6e96 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e96
        have b6e110 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e98
             grind)
          | exact superpose b6e98 b6e13
          | exact resolve b6e13 b6e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e98
        have b6e111 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e110
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e110
          | exact resolve b6e110 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110
        have b6e135 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X2 x
             have i₂ := b6e30 X1 X0 x
             grind)
          | (have i₁ := b6e12 X1 X1 X1
             have i₂ := b6e30 X1 X1 X2
             grind)
          | exact superpose b6e30 b6e12
          | exact resolve b6e12 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e246 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e111
             grind)
          | exact superpose b6e111 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111
        have b6e247 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e246
             have r₂ := b6e20
             grind)
          | exact resolve b6e246 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e246
        have b6e249 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e247
             have r₂ := b6e21
             grind)
          | exact resolve b6e247 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e247
        have b6e3703 : ∀ X0 : G, x = (M.op X0 (M.op (M.op y (M.op x x)) X0)) := by
          intro X0
          first
          | (have i₁ := b6e135 y x X0
             have i₂ := b6e249
             grind)
          | exact superpose b6e249 b6e135
          | exact resolve b6e135 b6e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e135 b6e249
        have b6e3822 : x = y := by
          first
          | (have i₁ := b6e3703 x
             have i₂ := b6e12 y x x
             grind)
          | exact superpose b6e12 b6e3703
          | exact resolve b6e3703 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3703
        have b6e3845 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e3822
             grind)
          | exact superpose b6e3822 b6e20
          | exact resolve b6e20 b6e3822
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3822
        have b6e3848 : False := by grind
        exact b6e3848
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : (σ y) = (k (σ x) (σ x)) := by grind
          clear b7e45
          have b7e48 : (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e47
            | exact resolve b7e47 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e49 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e46 x
               grind)
            | exact superpose b7e46 b7e48
            | exact resolve b7e48 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46 b7e48
          have b7e88 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e14
            | exact resolve b7e14 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e89 : y = (M.op x x) := by
            first
            | (have i₁ := b7e88
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e88
            | exact resolve b7e88 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e92 : False := by grind
          exact b7e92
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X2)) X1)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
               have i₂ := b8e13 X0 (M.op X0 (M.op X2 X2)) X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e42 (σ X0)
               grind)
            | exact superpose b8e42 b8e19
            | exact resolve b8e19 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e44
            | exact resolve b8e44 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b8e74 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e55 X0 X1
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e55
            | (have j0 := b8e55 X0 X1
               grind)
            | exact resolve b8e55 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e74 X0 X1
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e74
            | (have j0 := b8e74 X0 X1
               grind)
            | exact resolve b8e74 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49 b8e74
          have b8e140 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 (M.op X3 X3) X2
               have i₂ := b8e28 (M.op X1 (M.op X2 X2)) X0 X3
               grind)
            | (have i₁ := b8e13 X0 (M.op X0 (M.op X0 (M.op X2 X2))) X2
               have i₂ := b8e28 X0 (M.op X0 (M.op X2 X2)) X2
               grind)
            | exact superpose b8e28 b8e13
            | exact resolve b8e13 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28
          have b8e144 : ∀ X1 X3 : G, (M.op (M.op X3 X3) X1) = X1 := by
            intro X1 X3
            first
            | (have i₁ := b8e140 x X1 x X3
               have i₂ := b8e13 X1 x x
               grind)
            | exact superpose b8e13 b8e140
            | exact resolve b8e140 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e161 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (M.op X1 X1) X0 X1
               have i₂ := b8e144 X0 (M.op X1 X1)
               grind)
            | exact superpose b8e144 b8e13
            | exact resolve b8e13 b8e144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144
          have b8e270 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e161 X0 X1
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e161 X0 X1
               grind)
            | exact superpose b8e161 b8e16
            | (have j0 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e161 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e161 X0 X0
               grind)
            | exact resolve b8e16 b8e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161
          have b8e280 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e270 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e270
          have b8e442 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X1
               have i₂ := b8e280 X0 (σ X1)
               grind)
            | exact superpose b8e280 b8e19
            | exact resolve b8e19 b8e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e280
          have b8e457 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e442 X0 X1
               have i₂ := b8e42 X1
               grind)
            | exact superpose b8e42 b8e442
            | exact resolve b8e442 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e442
          have b8e1015 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e76 x y
               grind)
            | exact superpose b8e76 b8e23
            | (have j1 := b8e76 x y
               grind)
            | exact resolve b8e23 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e1035 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e1015
               have r₂ := b8e457 (σ x) x
               grind)
            | exact resolve b8e1015 b8e457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1015
          have b8e1170 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e457 (σ x) X0
               grind)
            | exact superpose b8e457 b8e24
            | exact resolve b8e24 b8e457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e457
          have b8e11639 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1035
               grind)
            | exact superpose b8e1035 b8e20
            | exact resolve b8e20 b8e1035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1035
          have b8e11670 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e11639
               have r₂ := b8e1170 x
               grind)
            | exact resolve b8e11639 b8e1170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1170 b8e11639
          have b8e11697 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e11670
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e11670
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e11670 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11670
          have b8e11698 : (M.op x x) = (M.op y x) ∨ y = (M.op x x) := by grind
          clear b8e11697
          have b8e11703 : y = (M.op x x) := by
            first
            | (have r₁ := b8e11698
               have r₂ := b8e21
               grind)
            | exact resolve b8e11698 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11698
          have b8e11708 : False := by grind
          exact b8e11708

/-- `Equation1977`: `x = (y ◇ (z ◇ y)) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyx_x_pxy_Equation1977 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1977 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1977.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) (M.op X0 X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op y x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e26 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op X1 (M.op (M.op X0 X2) X1)) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X3 (M.op X2 X3)) X1 (M.op X0 X2)
           have i₂ := b0e11 X0 X3 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k x y) := by
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
      have b0e43 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e45 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e43
      have b0e46 : (M.op y y) = (k x y) := by grind
      clear b0e41
      have b0e47 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e45
        | exact resolve b0e45 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e48 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e47
        | exact resolve b0e47 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e47
      have b0e215 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e26 x x X1 X0
           have i₂ := b0e26 x x X1 X2
           grind)
        | exact superpose b0e26 b0e26
        | exact resolve b0e26 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e512 : ∀ X0 : G, (M.op x (M.op y y)) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e215 X0 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e215
        | exact resolve b0e215 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e546 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X3) X2)) (M.op X0 (M.op X1 X0))) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 X2 (M.op X1 X3)
           have i₂ := b0e215 X3 X1 X0
           grind)
        | (have i₁ := b0e11 X3 X2 (M.op X1 X3)
           have i₂ := b0e215 X0 X1 X3
           grind)
        | exact superpose b0e215 b0e11
        | exact resolve b0e11 b0e215
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e215
      have b0e916 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op (M.op y y) X1)) (M.op X0 (M.op y X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X1 (M.op y y)
           have i₂ := b0e512 X0
           grind)
        | exact superpose b0e512 b0e11
        | exact resolve b0e11 b0e512
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e512
      have b0e960 : x = y := by
        first
        | (have i₁ := b0e916 x x
           have i₂ := b0e546 x y x y
           grind)
        | exact superpose b0e546 b0e916
        | exact resolve b0e916 b0e546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e546 b0e916
      have b0e1139 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e960
           grind)
        | exact superpose b0e960 b0e18
        | exact resolve b0e18 b0e960
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e960
      have b0e1149 : False := by grind
      exact b0e1149
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) (M.op X0 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op y x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e30 : ∀ X0 : G, (M.op (M.op x (M.op y y)) (M.op X0 y)) = X0 := by
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
        have b1e52 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k x y) := by
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
        have b1e55 : (M.op y y) = (k x y) := by grind
        clear b1e52
        have b1e71 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e73 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e71
        have b1e74 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e73
             have r₂ := b1e21
             grind)
          | exact resolve b1e73 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e75 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e74
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e74
          | exact resolve b1e74 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e76 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e75
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e75
          | exact resolve b1e75 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e75
        have b1e104 : (M.op y y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e13
          | exact resolve b1e13 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e105 : x = (M.op y y) := by
          first
          | (have i₁ := b1e104
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e104
          | exact resolve b1e104 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104
        have b1e131 : y = (M.op (M.op x x) x) := by
          first
          | (have i₁ := b1e30 y
             have i₂ := b1e105
             grind)
          | exact superpose b1e105 b1e30
          | exact resolve b1e30 b1e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e135 : ∀ X0 : G, (M.op (M.op y x) (M.op X0 y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e105
             grind)
          | exact superpose b1e105 b1e12
          | exact resolve b1e12 b1e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e137 : ∀ X0 : G, (M.op (M.op y y) (M.op X0 y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e135 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e135
          | exact resolve b1e135 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e135
        have b1e139 : ∀ X0 : G, (M.op x (M.op X0 y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e137 X0
             have i₂ := b1e105
             grind)
          | exact superpose b1e105 b1e137
          | exact resolve b1e137 b1e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e137
        have b1e167 : y = (M.op x x) := by
          first
          | (have i₁ := b1e139 y
             have i₂ := b1e105
             grind)
          | exact superpose b1e105 b1e139
          | exact resolve b1e139 b1e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139
        have b1e187 : y = (M.op y x) := by
          first
          | (have i₁ := b1e131
             have i₂ := b1e167
             grind)
          | exact superpose b1e167 b1e131
          | exact resolve b1e131 b1e167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131 b1e167
        have b1e274 : y = (M.op y y) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e187
             grind)
          | exact superpose b1e187 b1e20
          | exact resolve b1e20 b1e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e187
        have b1e377 : x = y := by
          first
          | (have i₁ := b1e105
             have i₂ := b1e274
             grind)
          | exact superpose b1e274 b1e105
          | exact resolve b1e105 b1e274
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105 b1e274
        have b1e404 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e377
             grind)
          | exact superpose b1e377 b1e21
          | exact resolve b1e21 b1e377
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e377
        have b1e416 : False := by grind
        exact b1e416
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) (M.op X0 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e20 : (M.op y x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op X1 (M.op (M.op X0 X2) X1)) X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X3 (M.op X2 X3)) X1 (M.op X0 X2)
             have i₂ := b2e12 X0 X3 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e224 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e32 x x X1 X0
             have i₂ := b2e32 x x X1 X2
             grind)
          | exact superpose b2e32 b2e32
          | exact resolve b2e32 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e388 : ∀ X0 : G, (M.op x (M.op y y)) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e224 X0 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e224
          | exact resolve b2e224 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e419 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X3) X2)) (M.op X0 (M.op X1 X0))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 X2 (M.op X1 X3)
             have i₂ := b2e224 X3 X1 X0
             grind)
          | (have i₁ := b2e12 X3 X2 (M.op X1 X3)
             have i₂ := b2e224 X0 X1 X3
             grind)
          | exact superpose b2e224 b2e12
          | exact resolve b2e12 b2e224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e224
        have b2e719 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op (M.op y y) X1)) (M.op X0 (M.op y X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 x X1 (M.op y y)
             have i₂ := b2e388 X0
             grind)
          | exact superpose b2e388 b2e12
          | exact resolve b2e12 b2e388
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e388
        have b2e761 : x = y := by
          first
          | (have i₁ := b2e719 x x
             have i₂ := b2e419 x y x y
             grind)
          | exact superpose b2e419 b2e719
          | exact resolve b2e719 b2e419
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e419 b2e719
        have b2e908 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e761
             grind)
          | exact superpose b2e761 b2e21
          | exact resolve b2e21 b2e761
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e761
        have b2e917 : False := by grind
        exact b2e917
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) (M.op X0 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e30 : ∀ X0 : G, (M.op (M.op y x) (M.op X0 x)) = X0 := by
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
        have b3e32 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) x) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e43
        have b3e47 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e46
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e46
          | exact resolve b3e46 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e56 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
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
        have b3e61 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by grind
        clear b3e56
        have b3e63 : x = (k x y) := by
          first
          | (have r₁ := b3e61
             have r₂ := b3e20
             grind)
          | exact resolve b3e61 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e108 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e15
          | exact resolve b3e15 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e111 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e108
        have b3e114 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e111
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e111
          | exact resolve b3e111 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111
        have b3e119 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e114
             have i₂ := b3e45 y
             grind)
          | exact superpose b3e45 b3e114
          | exact resolve b3e114 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e114
        have b3e121 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e119
             have i₂ := b3e63
             grind)
          | exact superpose b3e63 b3e119
          | exact resolve b3e119 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63 b3e119
        have b3e125 : (M.op y y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (M.op y y)
             have i₂ := b3e121
             grind)
          | exact superpose b3e121 b3e13
          | exact resolve b3e13 b3e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e121
        have b3e126 : x = (M.op y y) := by
          first
          | (have i₁ := b3e125
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e125
          | exact resolve b3e125 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e125
        have b3e170 : x = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b3e32 y
             have i₂ := b3e126
             grind)
          | exact superpose b3e126 b3e32
          | exact resolve b3e32 b3e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e232 : (M.op y x) = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b3e30 (M.op y x)
             have i₂ := b3e170
             grind)
          | exact superpose b3e170 b3e30
          | exact resolve b3e30 b3e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e240 : x = (M.op y x) := by
          first
          | (have i₁ := b3e232
             have i₂ := b3e170
             grind)
          | exact superpose b3e170 b3e232
          | exact resolve b3e232 b3e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e170 b3e232
        have b3e285 : x ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e240
             grind)
          | exact superpose b3e240 b3e20
          | exact resolve b3e20 b3e240
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e240
        have b3e300 : False := by grind
        exact b3e300
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
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e44 (σ X0)
               grind)
            | exact superpose b5e44 b5e19
            | exact resolve b5e19 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e47 X0
               have i₂ := b5e44 X0
               grind)
            | exact superpose b5e44 b5e47
            | exact resolve b5e47 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e47
          have b5e53 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
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
          have b5e57 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by grind
          clear b5e53
          have b5e58 : x = (k x y) := by
            first
            | (have r₁ := b5e57
               have r₂ := b5e21
               grind)
            | exact resolve b5e57 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e64 X0 X1
               have i₂ := b5e50 X1
               grind)
            | exact superpose b5e50 b5e64
            | (have j0 := b5e64 X0 X1
               grind)
            | exact resolve b5e64 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e829 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e182735 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e829 x y
               have i₂ := b5e58
               grind)
            | exact superpose b5e58 b5e829
            | (have j0 := b5e829 x y
               grind)
            | exact resolve b5e829 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58 b5e829
          have b5e182738 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e182735
          have b5e182741 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b5e182738
               have r₂ := b5e24
               grind)
            | exact resolve b5e182738 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e182738
          have b5e182746 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e182741
               grind)
            | exact superpose b5e182741 b5e23
            | exact resolve b5e23 b5e182741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e182741
          have b5e182928 : False := by grind
          exact b5e182928
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) (M.op X0 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e50 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e50
        have b6e53 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e52
          | exact resolve b6e52 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e73 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e15
          | exact resolve b6e15 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e77 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e73
        have b6e78 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e77
          | exact resolve b6e77 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e79 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e51 y
             grind)
          | exact superpose b6e51 b6e78
          | exact resolve b6e78 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e78
        have b6e110 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e79
             grind)
          | exact superpose b6e79 b6e13
          | exact resolve b6e13 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e111 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e110
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e110
          | exact resolve b6e110 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110
        have b6e150 : (M.op x y) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e111
             grind)
          | exact superpose b6e111 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111
        have b6e151 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e150
             have r₂ := b6e20
             grind)
          | exact resolve b6e150 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e150
        have b6e153 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e151
             have r₂ := b6e21
             grind)
          | exact resolve b6e151 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e151
        have b6e199 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b6e12 x X0 y
             have i₂ := b6e153
             grind)
          | exact superpose b6e153 b6e12
          | exact resolve b6e12 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e205 : x = y := by
          first
          | (have i₁ := b6e199 x
             have i₂ := b6e12 y x y
             grind)
          | exact superpose b6e12 b6e199
          | exact resolve b6e199 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e199
        have b6e263 : (M.op y y) ≠ (M.op y y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e205
             grind)
          | exact superpose b6e205 b6e20
          | exact resolve b6e20 b6e205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e205
        have b6e268 : False := by grind
        exact b6e268
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e58 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e56
          have b7e59 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e23
               grind)
            | exact resolve b7e58 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e60 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e59
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e59
            | exact resolve b7e59 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e73 : (σ (M.op x y)) = (σ x) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e60
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e60 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e86 : (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e73
               have r₂ := b7e25
               grind)
            | exact resolve b7e73 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e73
          have b7e89 : x = (M.op x y) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e21
               grind)
            | exact resolve b7e86 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e90 : False := by grind
          exact b7e90
        · have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e42 (σ X0)
               grind)
            | exact superpose b8e42 b8e19
            | exact resolve b8e19 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e44
            | exact resolve b8e44 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e44
          have b8e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e69 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e69
            | (have j0 := b8e69 X0 X1
               grind)
            | exact resolve b8e69 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e911 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e86 x y
               grind)
            | exact superpose b8e86 b8e20
            | (have j1 := b8e86 x y
               grind)
            | exact resolve b8e20 b8e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e1004 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e911
               have r₂ := b8e24
               grind)
            | exact resolve b8e911 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e911
          have b8e16360 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1004
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1004
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1004 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1004
          have b8e16369 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e16360
          have b8e16374 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e16369
               have r₂ := b8e21
               grind)
            | exact resolve b8e16369 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16369
          have b8e16375 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e16374
               have r₂ := b8e22
               grind)
            | exact resolve b8e16374 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16374
          have b8e16378 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e16375
               grind)
            | exact superpose b8e16375 b8e23
            | exact resolve b8e23 b8e16375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16375
          have b8e16477 : False := by grind
          exact b8e16477

/-- `Equation2306`: `x = (y ◇ (x ◇ (y ◇ z))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_y_pxy_pyx_Equation2306 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2306 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2306.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 : G, (M.op (M.op y (M.op X0 x)) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op (M.op (σ y) (M.op X0 (σ x))) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : y = (M.op (M.op y x) y) := by
        first
        | (have i₁ := b0e33 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e33
        | exact resolve b0e33 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e48 : y = (M.op x y) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e39
        | exact resolve b0e39 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e98 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
        first
        | (have i₁ := b0e34 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e107 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e98
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e98
        | exact resolve b0e98 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98
      have b0e112 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e107
           grind)
        | exact superpose b0e107 b0e18
        | exact resolve b0e18 b0e107
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107
      have b0e117 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e112
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e112
        | exact resolve b0e112 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e112
      have b0e118 : False := by grind
      exact b0e118
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
        have b1e26 : y = (k x y) := by grind
        clear b1e24
        have b1e30 : ∀ X0 : G, (M.op (M.op y (M.op X0 x)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : y = (M.op (M.op y x) y) := by
          first
          | (have i₁ := b1e30 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e30
          | exact resolve b1e30 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e45 : y = (M.op x y) := by
          first
          | (have i₁ := b1e36
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e36
          | exact resolve b1e36 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e60 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        have b1e62 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e60
             have r₂ := b1e21
             grind)
          | exact resolve b1e60 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e63 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e62
          | exact resolve b1e62 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e64 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e63
          | exact resolve b1e63 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e63
        have b1e67 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e64
             grind)
          | exact superpose b1e64 b1e19
          | exact resolve b1e19 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e72 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e67
             have i₂ := b1e45
             grind)
          | exact superpose b1e45 b1e67
          | exact resolve b1e67 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e67
        have b1e73 : False := by grind
        exact b1e73
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
        have b2e28 : ∀ X0 : G, (M.op (M.op y (M.op X0 x)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X3 X0)) X3) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 (M.op X1 (M.op X0 (M.op X1 X2))) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X0 (M.op X1 X2))) = (k X0 (M.op X1 (M.op X0 (M.op X1 X2)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
             grind)
          | (have r₁ := b2e15 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
             have r₂ := b2e12 X0 X1 X2
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (k X0 (M.op X1 (M.op X0 (M.op X1 X2)))) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e31 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e33 : y = (M.op (M.op y x) y) := by
          first
          | (have i₁ := b2e28 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e28
          | exact resolve b2e28 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e42 : y = (M.op x y) := by
          first
          | (have i₁ := b2e33
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e33
          | exact resolve b2e33 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e51 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
        have b2e53 : y ≠ y ∨ x = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e42
             grind)
          | exact resolve b2e15 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e54 : x = (k y x) := by grind
        clear b2e53
        have b2e84 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e27 X0 X1
             have i₂ := b2e17 X1 (τ X0)
             grind)
          | exact superpose b2e17 b2e27
          | (have j1 := b2e17 X1 (τ X0)
             grind)
          | exact resolve b2e27 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X3 X4))) = (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) (M.op X3 (M.op X0 (M.op X3 X4)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e29 X0 X1 X2 (M.op X3 (M.op X0 (M.op X3 X4)))
             have i₂ := b2e12 X0 X3 X4
             grind)
          | exact superpose b2e12 b2e29
          | exact resolve b2e29 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e120 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op X2 (M.op X1 X3))) (M.op X0 X2)) (M.op X4 X0)) X4) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e12 X4 (M.op (M.op X1 (M.op X2 (M.op X1 X3))) (M.op X0 X2)) X0
             have i₂ := b2e29 X2 X1 X3 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e133 : ∀ X0 X3 X4 : G, (M.op X3 (M.op X0 (M.op X3 X4))) = (M.op X0 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
          intro X0 X3 X4
          first
          | (have i₁ := b2e114 X0 x x X3 X4
             have i₂ := b2e12 X0 x x
             grind)
          | exact superpose b2e12 b2e114
          | exact resolve b2e114 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e114
        have b2e135 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e89 (k (τ X0) X1) X2
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e89
          | exact resolve b2e89 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e89
        have b2e150 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 x)) (M.op X1 X0)) = (k X1 (M.op (M.op y (M.op X0 x)) (M.op X1 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 (M.op y (M.op X0 x)) X0
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e32
          | exact resolve b2e32 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e275 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e51 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e276 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e275
             have r₂ := b2e21
             grind)
          | exact resolve b2e275 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e275
        have b2e277 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e276
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e276
          | exact resolve b2e276 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e276
        have b2e278 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e277
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e277
          | exact resolve b2e277 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e277
        have b2e466 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e47 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1618 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 (M.op X0 X2)
             have i₂ := b2e133 X1 X0 X2
             grind)
          | exact superpose b2e133 b2e12
          | exact resolve b2e12 b2e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e133
        have b2e2720 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X3 X0)) X3) = X3 := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e120 X0 (M.op X0 X1) X1 x X3
             have i₂ := b2e1618 (M.op X0 X1) X1 x
             grind)
          | exact superpose b2e1618 b2e120
          | exact resolve b2e120 b2e1618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120
        have b2e2721 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e29 X1 (M.op X0 X1) x X0
             have i₂ := b2e1618 (M.op X0 X1) X1 x
             grind)
          | exact superpose b2e1618 b2e29
          | exact resolve b2e29 b2e1618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e1618
        have b2e2844 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e2721 (σ X1) (σ X1)
             have i₂ := b2e47 X0 X1
             grind)
          | exact superpose b2e47 b2e2721
          | (have j1 := b2e47 X0 X1
             grind)
          | exact resolve b2e2721 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e2907 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e2844 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2844
        have b2e3530 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 x)) X0) = (k (M.op X0 X1) (M.op (M.op y (M.op X0 x)) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e150 X0 (M.op X0 X1)
             have i₂ := b2e2721 X0 X1
             grind)
          | exact superpose b2e2721 b2e150
          | exact resolve b2e150 b2e2721
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150
        have b2e3602 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e3530 X0 X1
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e3530
          | exact resolve b2e3530 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e3530
        have b2e3682 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e27 X0 (M.op (τ X0) X1)
             have i₂ := b2e3602 (τ X0) X1
             grind)
          | exact superpose b2e3602 b2e27
          | exact resolve b2e27 b2e3602
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e3602
        have b2e3683 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e3682 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e3682
          | exact resolve b2e3682 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3682
        have b2e4470 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e2721 X1 X1
             have i₂ := b2e84 X0 X1
             grind)
          | exact superpose b2e84 b2e2721
          | (have j1 := b2e84 X0 X1
             grind)
          | exact resolve b2e2721 b2e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e4488 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e4470 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4470
        have b2e10161 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e2720 (σ x) X0 (σ y)
             have i₂ := b2e278
             grind)
          | exact superpose b2e278 b2e2720
          | exact resolve b2e2720 b2e278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e278 b2e2720
        have b2e210490 : ∀ X0 X1 : G, (k (k (σ X0) X1) X1) = X1 ∨ (M.op (τ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e3683 X1 X0
             have i₂ := b2e4488 X1 X0
             grind)
          | exact superpose b2e4488 b2e3683
          | (have j1 := b2e4488 X1 X0
             grind)
          | exact resolve b2e3683 b2e4488
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3683 b2e4488
        have b2e211358 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k (τ (σ X1)) X0) (τ (σ X0))) ∨ (M.op (τ (σ X0)) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e135 (σ X1) X0 (σ X0)
             have i₂ := b2e210490 X1 (σ X0)
             grind)
          | exact superpose b2e210490 b2e135
          | (have j1 := b2e210490 X1 (σ X0)
             grind)
          | exact resolve b2e135 b2e210490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e210490
        have b2e211407 : ∀ X0 X1 : G, (k (k (τ (σ X1)) X0) X0) = X0 ∨ (M.op (τ (σ X0)) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e211358 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e211358
          | (have j0 := b2e211358 X0 X1
             grind)
          | exact resolve b2e211358 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e211358
        have b2e211439 : ∀ X0 X1 : G, (k (k X1 X0) X0) = X0 ∨ (M.op (τ (σ X0)) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e211407 X0 X1
             have i₂ := b2e13 X1
             grind)
          | exact superpose b2e13 b2e211407
          | (have j0 := b2e211407 X0 X1
             grind)
          | exact resolve b2e211407 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e211407
        have b2e211462 : ∀ X0 X1 : G, (k (k X1 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e211439 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e211439
          | (have j0 := b2e211439 X0 X1
             grind)
          | exact resolve b2e211439 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e211439
        have b2e212692 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k (τ X1) X0) (τ (σ X0))) ∨ (M.op (σ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e135 X1 X0 (σ X0)
             have i₂ := b2e211462 (σ X0) X1
             grind)
          | exact superpose b2e211462 b2e135
          | (have j1 := b2e211462 (σ X0) X1
             grind)
          | exact resolve b2e135 b2e211462
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e135 b2e211462
        have b2e212773 : ∀ X0 X1 : G, (k (k (τ X1) X0) X0) = X0 ∨ (M.op (σ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e212692 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e212692
          | (have j0 := b2e212692 X0 X1
             grind)
          | exact resolve b2e212692 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e212692
        have b2e219518 : ∀ X0 X1 : G, (k (k X0 X1) X1) = X1 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e212773 X1 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e212773
          | (have j0 := b2e212773 X1 (σ X0)
             grind)
          | exact resolve b2e212773 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e212773
        have b2e226784 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e219518 y x
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e219518
          | (have j0 := b2e219518 y x
             grind)
          | exact resolve b2e219518 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e219518
        have b2e228892 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e2721 (σ x) (σ y)
             have i₂ := b2e226784
             grind)
          | exact superpose b2e226784 b2e2721
          | exact resolve b2e2721 b2e226784
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e226784
        have b2e228988 : x = (k x x) := by
          first
          | (have r₁ := b2e228892
             have r₂ := b2e21
             grind)
          | exact resolve b2e228892 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e228892
        have b2e230742 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e466 x x
             have i₂ := b2e228988
             grind)
          | exact superpose b2e228988 b2e466
          | (have j0 := b2e466 x x
             grind)
          | exact resolve b2e466 b2e228988
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e466 b2e228988
        have b2e230758 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e230742
        have b2e230759 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e230758
        have b2e234964 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
          first
          | (have i₁ := b2e10161 (σ x)
             have i₂ := b2e230759
             grind)
          | exact superpose b2e230759 b2e10161
          | exact resolve b2e10161 b2e230759
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10161 b2e230759
        have b2e837289 : (σ y) = (M.op (σ (k y x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e234964
             have i₂ := b2e2907 x y
             grind)
          | exact superpose b2e2907 b2e234964
          | (have j1 := b2e2907 (k y x) y
             grind)
          | exact resolve b2e234964 b2e2907
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2907 b2e234964
        have b2e837334 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e837289
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e837289
          | exact resolve b2e837289 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e837289
        have b2e837335 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e837334
        have b2e839274 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e2721 (σ x) (σ y)
             have i₂ := b2e837335
             grind)
          | exact superpose b2e837335 b2e2721
          | exact resolve b2e2721 b2e837335
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2721 b2e837335
        have b2e839507 : False := by grind
        exact b2e839507
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e27 : (σ y) = (σ (k x y)) := by
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
        have b3e28 : (k x y) = (τ (σ y)) := by
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
        have b3e29 : y = (k x y) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e28
          | exact resolve b3e28 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e36 : ∀ X0 : G, (M.op (M.op x (M.op X0 y)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e63 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by grind
        have b3e66 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e63
             have r₂ := b3e20
             grind)
          | exact resolve b3e63 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e67 : y = (M.op x y) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e29
             grind)
          | exact superpose b3e29 b3e66
          | exact resolve b3e66 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e66
        have b3e68 : x = (M.op (M.op x y) x) := by
          first
          | (have i₁ := b3e36 x
             have i₂ := b3e67
             grind)
          | exact superpose b3e67 b3e36
          | exact resolve b3e36 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e72 : x = (M.op y x) := by
          first
          | (have i₁ := b3e68
             have i₂ := b3e67
             grind)
          | exact superpose b3e67 b3e68
          | exact resolve b3e68 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67 b3e68
        have b3e73 : False := by grind
        exact b3e73
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e66 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          have b4e67 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by grind
          have b4e70 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e67
               have r₂ := b4e21
               grind)
            | exact resolve b4e67 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e71 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e66
               have r₂ := b4e23
               grind)
            | exact resolve b4e66 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e72 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e71
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e71
            | exact resolve b4e71 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e73 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e70
               grind)
            | exact superpose b4e70 b4e72
            | exact resolve b4e72 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70 b4e72
          have b4e74 : False := by grind
          exact b4e74
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e33 : ∀ X0 : G, (M.op (M.op x (M.op X0 y)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X3 X0)) X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X1 (M.op X0 (M.op X1 X2))) X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op x (M.op X0 X1))) y) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e34 x X0 X1 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e34
            | exact resolve b5e34 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 y)) = (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) (M.op x (M.op X0 y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X1 X2 (M.op x (M.op X0 y))
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e34
            | exact resolve b5e34 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e88 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op X0 (M.op x (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b5e79 X0 x x
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e79
            | exact resolve b5e79 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e556 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op X0 y)) y) x) := by
            intro X0
            first
            | (have i₁ := b5e77 X0 y
               have i₂ := b5e88 X0
               grind)
            | exact superpose b5e88 b5e77
            | exact resolve b5e77 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77 b5e88
          have b5e1069 : x = (M.op y x) := by
            first
            | (have i₁ := b5e556 y
               have i₂ := b5e33 y
               grind)
            | exact superpose b5e33 b5e556
            | exact resolve b5e556 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e556
          have b5e1095 : False := by grind
          exact b5e1095
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
        have b6e27 : (k x y) = (τ (σ y)) := by
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
        have b6e28 : y = (k x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e27
          | exact resolve b6e27 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e39 : ∀ X0 : G, (M.op (M.op (σ y) (M.op X0 (σ x))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
        clear b6e28
        have b6e64 : y = (M.op y x) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e58
             have r₂ := b6e21
             grind)
          | exact resolve b6e58 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e67 : y = (M.op y x) := by
          first
          | (have r₁ := b6e64
             have r₂ := b6e20
             grind)
          | exact resolve b6e64 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e70 : ∀ X0 : G, (M.op (M.op y (M.op X0 y)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 y x
             have i₂ := b6e67
             grind)
          | exact superpose b6e67 b6e12
          | exact resolve b6e12 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e72 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e78 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
          first
          | (have i₁ := b6e39 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e39
          | exact resolve b6e39 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e83 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e78
          | exact resolve b6e78 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e118 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e83
             grind)
          | exact superpose b6e83 b6e19
          | exact resolve b6e19 b6e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e122 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e83
             grind)
          | exact superpose b6e83 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | (have r₁ := b6e15 (σ y) (σ x)
             have r₂ := b6e83
             grind)
          | exact resolve b6e15 b6e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e123 : (σ x) = (k (σ y) (σ x)) := by grind
        clear b6e122
        have b6e124 : (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e123
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e123
          | exact resolve b6e123 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e167 : (k y x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e124
             grind)
          | exact superpose b6e124 b6e13
          | exact resolve b6e13 b6e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e124
        have b6e168 : x = (k y x) := by
          first
          | (have i₁ := b6e167
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e167
          | exact resolve b6e167 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e167
        have b6e178 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e74 x y
             have i₂ := b6e168
             grind)
          | exact superpose b6e168 b6e74
          | (have j0 := b6e74 y x
             grind)
          | exact resolve b6e74 b6e168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74 b6e168
        have b6e180 : y = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e178
             have r₂ := b6e20
             grind)
          | exact resolve b6e178 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e178
        have b6e535 : (σ y) ≠ (σ y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e118
             have i₂ := b6e180
             grind)
          | exact superpose b6e180 b6e118
          | exact resolve b6e118 b6e180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e118 b6e180
        have b6e550 : x = (M.op x y) := by grind
        clear b6e535
        have b6e573 : x = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b6e70 x
             have i₂ := b6e550
             grind)
          | exact superpose b6e550 b6e70
          | exact resolve b6e70 b6e550
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70 b6e550
        have b6e584 : x = (M.op y x) := by
          first
          | (have i₁ := b6e573
             have i₂ := b6e67
             grind)
          | exact superpose b6e67 b6e573
          | exact resolve b6e573 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67 b6e573
        have b6e585 : False := by grind
        exact b6e585
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e45 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X1 X1
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X1
               have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e16 (M.op X0 X0) X1
               have r₂ := b7e18 X0 (M.op X1 (M.op X0 X0))
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e57 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          have b7e61 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e23
               grind)
            | exact resolve b7e57 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e62 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e61
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e61
            | exact resolve b7e61 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e63 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e62
               grind)
            | exact superpose b7e62 b7e20
            | exact resolve b7e20 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e77 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e63
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e63
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e63 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e78 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e22
               grind)
            | exact resolve b7e77 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e79 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e78
               have r₂ := b7e21
               grind)
            | exact resolve b7e78 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e184 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e45 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e185 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e184 X0
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e184 X0
               have r₂ := b7e16 X0 X0
               grind)
            | exact resolve b7e184 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e184
          have b7e363 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e42 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e42
            | exact resolve b7e42 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e425 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e363
          have b7e443 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e425
               grind)
            | exact superpose b7e425 b7e14
            | exact resolve b7e14 b7e425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e425
          have b7e456 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e443
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e443
            | exact resolve b7e443 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e443
          have b7e507 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e185 x
               have i₂ := b7e456
               grind)
            | exact superpose b7e456 b7e185
            | exact resolve b7e185 b7e456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e185 b7e456
          have b7e522 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e507
               have r₂ := b7e22
               grind)
            | exact resolve b7e507 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e507
          have b7e592 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e522
               grind)
            | exact superpose b7e522 b7e14
            | exact resolve b7e14 b7e522
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e522
          have b7e607 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e592
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e592
            | exact resolve b7e592 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e592
          have b7e608 : x = y := by grind
          clear b7e607
          have b7e642 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e79
               have i₂ := b7e608
               grind)
            | exact superpose b7e608 b7e79
            | exact resolve b7e79 b7e608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e608
          have b7e644 : False := by grind
          exact b7e644
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b8e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X3 X0)) X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 (M.op X1 (M.op X0 (M.op X1 X2))) X0
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e39 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e18 (τ X1) X0
               grind)
            | exact superpose b8e18 b8e26
            | (have j1 := b8e18 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e41 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X1
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 (M.op X0 X0) X1
               have r₂ := b8e18 X0 (M.op X1 (M.op X0 X0))
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e71 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X3 X4))) = (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) (M.op X3 (M.op X0 (M.op X3 X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e28 X0 X1 X2 (M.op X3 (M.op X0 (M.op X3 X4)))
               have i₂ := b8e13 X0 X3 X4
               grind)
            | exact superpose b8e13 b8e28
            | exact resolve b8e28 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e79 : ∀ X0 X3 X4 : G, (M.op X3 (M.op X0 (M.op X3 X4))) = (M.op X0 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
            intro X0 X3 X4
            first
            | (have i₁ := b8e71 X0 x x X3 X4
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e71
            | exact resolve b8e71 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e119 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e55 (σ X1) (σ X0)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e55
            | (have j0 := b8e55 (σ X1) (σ X0)
               grind)
            | exact resolve b8e55 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e168 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e41 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41
          have b8e169 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e168 X0
               have j1 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e168 X0
               have r₂ := b8e16 X0 X0
               grind)
            | exact resolve b8e168 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e168
          have b8e170 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e169 (σ x)
               have i₂ := b8e19 x x
               grind)
            | exact superpose b8e19 b8e169
            | exact resolve b8e169 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e169
          have b8e267 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X1 X1
               have i₂ := b8e38 X0 X1
               grind)
            | exact superpose b8e38 b8e38
            | (have j0 := b8e38 X0 X1
               have j1 := b8e38 X0 X1
               grind)
            | exact resolve b8e38 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38
          have b8e322 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e267 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e267
          have b8e678 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X0 X1 (M.op X0 X2)
               have i₂ := b8e79 X1 X0 X2
               grind)
            | exact superpose b8e79 b8e13
            | exact resolve b8e13 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e737 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e28 X1 (M.op X0 X1) x X0
               have i₂ := b8e678 (M.op X0 X1) X1 x
               grind)
            | exact superpose b8e678 b8e28
            | exact resolve b8e28 b8e678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28 b8e678
          have b8e865 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e737 (M.op X0 X1) X0
               have i₂ := b8e737 X0 X1
               grind)
            | exact superpose b8e737 b8e737
            | exact resolve b8e737 b8e737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e866 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e737 X1 X1
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e737 X0 X1
               have i₂ := b8e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b8e18 b8e737
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e737 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e872 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 (M.op X0 X1)
               have i₂ := b8e737 X0 X1
               grind)
            | exact superpose b8e737 b8e16
            | (have j0 := b8e16 X0 (M.op X0 X1)
               grind)
            | (have r₁ := b8e16 X0 (M.op X0 X1)
               have r₂ := b8e737 X0 X1
               grind)
            | exact resolve b8e16 b8e737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e900 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e872 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e872
          have b8e902 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e866 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e866
          have b8e3294 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e900 (τ X1) (τ X1)
               have i₂ := b8e39 X0 X1
               grind)
            | (have i₁ := b8e900 X0 X1
               have i₂ := b8e39 (M.op X0 X1) X1
               grind)
            | exact superpose b8e39 b8e900
            | (have j1 := b8e39 X0 X1
               grind)
            | exact resolve b8e900 b8e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39 b8e900
          have b8e3308 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e3294 X0 X1
               have j1 := b8e16 (τ X1) X0
               grind)
            | (have r₁ := b8e3294 X1 X1
               have r₂ := b8e16 (τ X1) X1
               grind)
            | exact resolve b8e3294 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3294
          have b8e7933 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e119 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e10738 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e322 x y
               grind)
            | exact superpose b8e322 b8e20
            | (have j1 := b8e322 x y
               grind)
            | exact resolve b8e20 b8e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322
          have b8e39182 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e3308 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e3308
            | exact resolve b8e3308 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3308
          have b8e39368 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e39182 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e39182
            | (have j0 := b8e39182 X0 X1
               grind)
            | exact resolve b8e39182 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39182
          have b8e40696 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X1 X0)
               have i₂ := b8e39368 X1 X0
               grind)
            | exact superpose b8e39368 b8e14
            | (have j1 := b8e39368 X1 X0
               grind)
            | exact resolve b8e14 b8e39368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e40805 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e40696 X0 X1
               have i₂ := b8e14 (M.op X0 X1)
               grind)
            | exact superpose b8e14 b8e40696
            | (have j0 := b8e40696 X0 X1
               grind)
            | exact resolve b8e40696 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40696
          have b8e41796 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e40805 (σ X1) (σ X0)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e40805
            | exact resolve b8e40805 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e41948 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e40805 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40805
          have b8e78831 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e737 (σ X0) (σ X0)
               have i₂ := b8e170 X0
               grind)
            | exact superpose b8e170 b8e737
            | (have j1 := b8e170 X0
               grind)
            | exact resolve b8e737 b8e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e170
          have b8e107601 : ∀ X0 : G, (σ (τ X0)) = (M.op (k X0 (σ (τ X0))) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e78831 (τ X0)
               have i₂ := b8e26 X0 (τ X0)
               grind)
            | exact superpose b8e26 b8e78831
            | exact resolve b8e78831 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e78831
          have b8e108080 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e107601 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e107601
            | (have j0 := b8e107601 X0
               grind)
            | exact resolve b8e107601 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107601
          have b8e108127 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e108080 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e108080
            | (have j0 := b8e108080 X0
               grind)
            | exact resolve b8e108080 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108080
          have b8e109157 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e737 (k X0 X0) X0
               have i₂ := b8e108127 X0
               grind)
            | exact superpose b8e108127 b8e737
            | (have j1 := b8e108127 X0
               grind)
            | exact resolve b8e737 b8e108127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108127
          have b8e173473 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e41796 y x
               grind)
            | exact superpose b8e41796 b8e20
            | (have j1 := b8e41796 y x
               grind)
            | exact resolve b8e20 b8e41796
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41796
          have b8e182269 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e173473
               have i₂ := b8e39368 y x
               grind)
            | exact superpose b8e39368 b8e173473
            | (have j1 := b8e39368 y x
               grind)
            | (have r₁ := b8e173473
               have r₂ := b8e39368 y x
               grind)
            | exact resolve b8e173473 b8e39368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39368 b8e173473
          have b8e182270 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by grind
          clear b8e182269
          have b8e182416 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e182270
               grind)
            | exact superpose b8e182270 b8e14
            | exact resolve b8e14 b8e182270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182270
          have b8e182490 : x = (M.op x y) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e182416
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e182416
            | exact resolve b8e182416 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182416
          have b8e182491 : x = (k y x) := by
            first
            | (have j1 := b8e41948 y x
               grind)
            | (have r₁ := b8e182490
               have r₂ := b8e41948 y x
               grind)
            | exact resolve b8e182490 b8e41948
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41948 b8e182490
          have b8e182645 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e902 x y
               have i₂ := b8e182491
               grind)
            | exact superpose b8e182491 b8e902
            | (have j0 := b8e902 x y
               grind)
            | exact resolve b8e902 b8e182491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e902
          have b8e182650 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e7933 x y
               have i₂ := b8e182491
               grind)
            | exact superpose b8e182491 b8e7933
            | (have j0 := b8e7933 y x
               grind)
            | exact resolve b8e7933 b8e182491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7933
          have b8e182670 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e182650
               have r₂ := b8e23
               grind)
            | exact resolve b8e182650 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182650
          have b8e183068 : x = (M.op y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e737 x y
               have i₂ := b8e182645
               grind)
            | exact superpose b8e182645 b8e737
            | exact resolve b8e737 b8e182645
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182645
          have b8e183199 : x = (M.op x y) := by
            first
            | (have r₁ := b8e183068
               have r₂ := b8e21
               grind)
            | exact resolve b8e183068 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e183068
          have b8e184276 : x = (M.op x x) := by
            first
            | (have i₁ := b8e865 x y
               have i₂ := b8e183199
               grind)
            | exact superpose b8e183199 b8e865
            | exact resolve b8e865 b8e183199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e865
          have b8e185389 : x ≠ y := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e184276
               grind)
            | exact superpose b8e184276 b8e22
            | exact resolve b8e22 b8e184276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184276
          have b8e212275 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e10738
               have i₂ := b8e182491
               grind)
            | exact superpose b8e182491 b8e10738
            | exact resolve b8e10738 b8e182491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10738 b8e182491
          have b8e212298 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e212275
               have r₂ := b8e182670
               grind)
            | exact resolve b8e212275 b8e182670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182670 b8e212275
          have b8e212302 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e212298
               have i₂ := b8e183199
               grind)
            | exact superpose b8e183199 b8e212298
            | exact resolve b8e212298 b8e183199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e183199 b8e212298
          have b8e212303 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y y)) := by grind
          clear b8e212302
          have b8e274690 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b8e737 (σ x) (σ y)
               have i₂ := b8e212303
               grind)
            | exact superpose b8e212303 b8e737
            | exact resolve b8e737 b8e212303
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e737 b8e212303
          have b8e274784 : (σ x) = (σ (k y y)) := by
            first
            | (have r₁ := b8e274690
               have r₂ := b8e23
               grind)
            | exact resolve b8e274690 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e274690
          have b8e275705 : (k y y) = (τ (σ x)) := by
            first
            | (have i₁ := b8e14 (k y y)
               have i₂ := b8e274784
               grind)
            | exact superpose b8e274784 b8e14
            | exact resolve b8e14 b8e274784
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e274784
          have b8e275806 : x = (k y y) := by
            first
            | (have i₁ := b8e275705
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e275705
            | exact resolve b8e275705 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e275705
          have b8e277259 : x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e109157 y
               have i₂ := b8e275806
               grind)
            | exact superpose b8e275806 b8e109157
            | exact resolve b8e109157 b8e275806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109157 b8e275806
          have b8e277332 : x = y := by
            first
            | (have r₁ := b8e277259
               have r₂ := b8e21
               grind)
            | exact resolve b8e277259 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e277259
          have b8e277340 : False := by grind
          exact b8e277340

/-- `Equation3272`: `x ◇ x = y ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pyx_pxy_Equation3272 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3272 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3272.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e40 : (M.op x y) = (k x y) := by grind
      have b0e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e45 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e41
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e41
        | exact resolve b0e41 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e46 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e40
           grind)
        | exact superpose b0e40 b0e45
        | exact resolve b0e45 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e45
      have b0e47 : False := by grind
      exact b0e47
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e45 : (M.op x y) = (k x y) := by grind
        have b1e49 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = X0 ∨ (k X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e16
          | (have j0 := b1e16 X0 y
             grind)
          | exact resolve b1e16 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e130 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e55 (σ X0)
             grind)
          | exact superpose b1e55 b1e18
          | (have j1 := b1e55 (σ X0)
             grind)
          | exact resolve b1e18 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e653 : x ≠ x ∨ x = y ∨ x = (k y y) := by
          first
          | (have i₁ := b1e54 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e54
          | (have j0 := b1e54 y
             grind)
          | (have r₁ := b1e54 y
             have r₂ := b1e20
             grind)
          | exact resolve b1e54 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e654 : x = (k y y) ∨ x = y := by grind
        clear b1e653
        have b1e2033 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e49 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e49
          | (have j0 := b1e49 (σ y)
             grind)
          | (have r₁ := b1e49 (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e49 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2038 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b1e49 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e2039 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
        clear b1e2033
        have b1e2040 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e2038
             have r₂ := b1e21
             grind)
          | exact resolve b1e2038 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2038
        have b1e2041 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have r₁ := b1e2039
             have r₂ := b1e21
             grind)
          | exact resolve b1e2039 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2039
        have b1e2047 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e2040
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e2040
          | exact resolve b1e2040 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2040
        have b1e2048 : (M.op (σ y) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e2041
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e2041
          | exact resolve b1e2041 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2041
        have b1e2054 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e2047
             have i₂ := b1e45
             grind)
          | exact superpose b1e45 b1e2047
          | exact resolve b1e2047 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e2047
        have b1e2066 : (σ x) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e2048
             grind)
          | exact superpose b1e2048 b1e21
          | exact resolve b1e21 b1e2048
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2072 : (k (σ (k x x)) (σ y)) = (M.op (σ (k x x)) (σ y)) := by grind
        have b1e2104 : (M.op (σ (k x x)) (σ y)) = (σ (k (k x x) y)) := by
          first
          | (have i₁ := b1e2072
             have i₂ := b1e18 (k x x) y
             grind)
          | exact superpose b1e18 b1e2072
          | exact resolve b1e2072 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2072
        have b1e8706 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e130 y
             grind)
          | exact superpose b1e130 b1e21
          | (have j1 := b1e130 y
             grind)
          | exact resolve b1e21 b1e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e130
        have b1e8837 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e8706
             have i₂ := b1e2048
             grind)
          | exact superpose b1e2048 b1e8706
          | exact resolve b1e8706 b1e2048
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8706
        have b1e8876 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e8837
             have i₂ := b1e654
             grind)
          | exact superpose b1e654 b1e8837
          | exact resolve b1e8837 b1e654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8837
        have b1e8889 : (σ y) = (σ (k x x)) ∨ x = y := by grind
        clear b1e8876
        have b1e9019 : (k x x) = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e8889
             grind)
          | exact superpose b1e8889 b1e13
          | exact resolve b1e13 b1e8889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8889
        have b1e9063 : y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e9019
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e9019
          | exact resolve b1e9019 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9019
        have b1e9774 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b1e2104
             have i₂ := b1e9063
             grind)
          | exact superpose b1e9063 b1e2104
          | exact resolve b1e2104 b1e9063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2104 b1e9063
        have b1e9792 : (σ (k x x)) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b1e9774
             have i₂ := b1e2048
             grind)
          | exact superpose b1e2048 b1e9774
          | exact resolve b1e9774 b1e2048
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2048 b1e9774
        have b1e10666 : (σ x) ≠ (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b1e2066
             have i₂ := b1e9792
             grind)
          | exact superpose b1e9792 b1e2066
          | exact resolve b1e2066 b1e9792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2066 b1e9792
        have b1e10951 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b1e10666
             have i₂ := b1e654
             grind)
          | exact superpose b1e654 b1e10666
          | exact resolve b1e10666 b1e654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e654 b1e10666
        have b1e10965 : (σ x) ≠ (σ x) ∨ x = y := by grind
        clear b1e10951
        have b1e10966 : x = y := by grind
        clear b1e10965
        have b1e11080 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e2054
             have i₂ := b1e10966
             grind)
          | exact superpose b1e10966 b1e2054
          | exact resolve b1e2054 b1e10966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2054 b1e10966
        have b1e11106 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e11080
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e11080
          | exact resolve b1e11080 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11080
        have b1e11119 : False := by grind
        exact b1e11119
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e41 : (M.op x y) = (k x y) := by grind
        have b2e87 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (σ x) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ x)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (M.op (σ x) (σ x)) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1822 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have j0 := b2e87 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e1823 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1822
             have r₂ := b2e21
             grind)
          | exact resolve b2e1822 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1822
        have b2e1828 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1823
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1823
          | exact resolve b2e1823 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1823
        have b2e1833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1828
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e1828
          | exact resolve b2e1828 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e1828
        have b2e1835 : False := by grind
        exact b2e1835
  · rcases eq_or_ne (M.op x x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : (M.op y y) = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e37 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e39 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e37
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e37
          | exact resolve b3e37 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e49 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op X0 X0) = x ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e21
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 X0 (σ y)
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e631 : x = (M.op y y) ∨ (k x y) = (M.op y x) := by
          first
          | (have j0 := b3e49 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e633 : (k x y) = (M.op y x) := by
          first
          | (have r₁ := b3e631
             have r₂ := b3e20
             grind)
          | exact resolve b3e631 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e631
        have b3e664 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e53 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e53
          | (have j0 := b3e53 (σ y)
             grind)
          | (have r₁ := b3e53 (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e53 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e666 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
        clear b3e664
        have b3e667 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e666
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e666
          | exact resolve b3e666 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e666
        have b3e816 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e667
             grind)
          | exact superpose b3e667 b3e13
          | exact resolve b3e13 b3e667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e667
        have b3e841 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e816
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e816
          | exact resolve b3e816 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e816
        have b3e938 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e55 y
             have i₂ := b3e841
             grind)
          | exact superpose b3e841 b3e55
          | (have j0 := b3e55 y
             grind)
          | exact resolve b3e55 b3e841
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e939 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e938
             have r₂ := b3e20
             grind)
          | exact resolve b3e938 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e938
        have b3e1027 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by grind
        clear b3e939
        have b3e1217 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e841
             have i₂ := b3e1027
             grind)
          | exact superpose b3e1027 b3e841
          | exact resolve b3e841 b3e1027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e841 b3e1027
        have b3e1220 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b3e1217
        have b3e1222 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e1220
             have r₂ := b3e20
             grind)
          | exact resolve b3e1220 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1220
        have b3e1413 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e39
             have i₂ := b3e1222
             grind)
          | exact superpose b3e1222 b3e39
          | exact resolve b3e39 b3e1222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e1414 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1222
             grind)
          | exact superpose b3e1222 b3e19
          | exact resolve b3e19 b3e1222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1415 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e1222
             grind)
          | exact superpose b3e1222 b3e13
          | exact resolve b3e13 b3e1222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1440 : x = y := by
          first
          | (have i₁ := b3e1415
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1415
          | exact resolve b3e1415 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1415
        have b3e1441 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e1414
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1414
          | exact resolve b3e1414 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1414
        have b3e1442 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e1413
             have i₂ := b3e633
             grind)
          | exact superpose b3e633 b3e1413
          | exact resolve b3e1413 b3e633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e633 b3e1413
        have b3e1444 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e1441
             have i₂ := b3e1222
             grind)
          | exact superpose b3e1222 b3e1441
          | exact resolve b3e1441 b3e1222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1441
        have b3e1445 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e1442
             have i₂ := b3e1440
             grind)
          | exact superpose b3e1440 b3e1442
          | exact resolve b3e1442 b3e1440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1442
        have b3e1446 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e1444
             have i₂ := b3e1440
             grind)
          | exact superpose b3e1440 b3e1444
          | exact resolve b3e1444 b3e1440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1440 b3e1444
        have b3e1447 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e1445
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1445
          | exact resolve b3e1445 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1445
        have b3e1448 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e1447
             have i₂ := b3e1222
             grind)
          | exact superpose b3e1222 b3e1447
          | exact resolve b3e1447 b3e1222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1222 b3e1447
        have b3e1449 : False := by grind
        exact b3e1449
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op y y) := by grind
          have b4e22 : (M.op y y) = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e29 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ y) (σ y)))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op X0 X0) = x ∨ (k x X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e62 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op y y) = X0 ∨ (k X0 x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 X0 y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 X0 (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e96 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X1 ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X1 X2
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X1 X2
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X0
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 (M.op X1 X1) X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e152 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e65 (σ X0)
               grind)
            | exact superpose b4e65 b4e19
            | (have j1 := b4e65 (σ X0)
               grind)
            | exact resolve b4e19 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65
          have b4e169 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op X0 X0))) = (M.op (σ x) (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e37 (M.op (σ y) (σ y))
               have i₂ := b4e13 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b4e13 b4e37
            | exact resolve b4e37 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e732 : (M.op y y) ≠ (M.op y y) ∨ x = (M.op y y) ∨ (M.op y y) = (k x x) := by
            first
            | (have i₁ := b4e59 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e59
            | (have j0 := b4e59 y
               grind)
            | (have r₁ := b4e59 x
               have r₂ := b4e22
               grind)
            | exact resolve b4e59 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e736 : x = (M.op y y) ∨ (M.op y y) = (k x x) := by grind
          clear b4e732
          have b4e738 : (M.op y y) = (k x x) := by
            first
            | (have r₁ := b4e736
               have r₂ := b4e21
               grind)
            | exact resolve b4e736 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e736
          have b4e758 : (M.op x y) = (k y x) ∨ y = (M.op y y) := by
            first
            | (have j0 := b4e62 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e2679 : (M.op (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e152 x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e152
            | exact resolve b4e152 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e152
          have b4e2767 : (M.op (σ y) (σ y)) = (σ (k x x)) := by
            first
            | (have r₁ := b4e2679
               have r₂ := b4e23
               grind)
            | exact resolve b4e2679 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2679
          have b4e2777 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e2767
               have i₂ := b4e738
               grind)
            | exact superpose b4e738 b4e2767
            | exact resolve b4e2767 b4e738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e738 b4e2767
          have b4e3364 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e64 (σ y)
               have i₂ := b4e2777
               grind)
            | exact superpose b4e2777 b4e64
            | (have j0 := b4e64 (σ y)
               grind)
            | exact resolve b4e64 b4e2777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e3373 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b4e3364
          have b4e3381 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e3373
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e3373
            | exact resolve b4e3373 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3373
          have b4e9783 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e96 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96
          have b4e9784 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e9783 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9783
          have b4e11828 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e3381
               grind)
            | exact superpose b4e3381 b4e20
            | exact resolve b4e20 b4e3381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3381
          have b4e19759 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          clear b4e9784
          have b4e20031 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e19759 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19759
          have b4e20174 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e20031 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20031
          have b4e20365 : ∀ X0 : G, (M.op x (M.op X0 (M.op y y))) ≠ (M.op x (M.op X0 (M.op y y))) ∨ (M.op x (M.op X0 (M.op y y))) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e20174 X0 X0
               have i₂ := b4e29 X0
               grind)
            | exact superpose b4e29 b4e20174
            | exact resolve b4e20174 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e20433 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e20174 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20174
          have b4e20491 : ∀ X0 : G, (M.op x (M.op X0 (M.op y y))) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e20365 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20365
          have b4e21007 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e20433 (σ X0)
               grind)
            | exact superpose b4e20433 b4e19
            | exact resolve b4e19 b4e20433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e21028 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e21007 X0
               have i₂ := b4e20433 X0
               grind)
            | exact superpose b4e20433 b4e21007
            | exact resolve b4e21007 b4e20433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21007
          have b4e21933 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (σ X0) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ X0) X1
               have i₂ := b4e21028 X0
               grind)
            | exact superpose b4e21028 b4e13
            | exact resolve b4e13 b4e21028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21028
          have b4e23066 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op x (M.op (τ X0) (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (τ X0)
               have i₂ := b4e20491 (τ X0)
               grind)
            | exact superpose b4e20491 b4e26
            | exact resolve b4e26 b4e20491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e20491
          have b4e23077 : ∀ X0 : G, (k X0 X0) = (σ (M.op x (M.op (τ X0) (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b4e23066 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e23066
            | exact resolve b4e23066 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23066
          have b4e26451 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op x (M.op (τ (σ X0)) (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e23077 (σ X0)
               grind)
            | exact superpose b4e23077 b4e19
            | exact resolve b4e19 b4e23077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23077
          have b4e26522 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op x (M.op X0 (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b4e26451 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e26451
            | exact resolve b4e26451 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26451
          have b4e26590 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op x (M.op X0 (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b4e26522 X0
               have i₂ := b4e20433 X0
               grind)
            | exact superpose b4e20433 b4e26522
            | exact resolve b4e26522 b4e20433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20433 b4e26522
          have b4e109670 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e11828
               have i₂ := b4e758
               grind)
            | exact superpose b4e758 b4e11828
            | exact resolve b4e11828 b4e758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e758 b4e11828
          have b4e109679 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e109670
          have b4e109956 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e109679
               grind)
            | exact superpose b4e109679 b4e14
            | exact resolve b4e14 b4e109679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109679
          have b4e110019 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e109956
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e109956
            | exact resolve b4e109956 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109956
          have b4e110020 : y = (M.op y y) := by grind
          clear b4e110019
          have b4e111849 : (M.op y (M.op (M.op (σ y) (σ y)) y)) = (M.op (σ x) (M.op y (M.op (M.op (σ y) (σ y)) y))) := by
            first
            | (have i₁ := b4e169 y
               have i₂ := b4e110020
               grind)
            | exact superpose b4e110020 b4e169
            | exact resolve b4e169 b4e110020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e169
          have b4e111953 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op y (M.op (σ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e21933 X0 y
               have i₂ := b4e110020
               grind)
            | exact superpose b4e110020 b4e21933
            | exact resolve b4e21933 b4e110020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21933
          have b4e111967 : (σ y) = (σ (M.op x (M.op y y))) := by
            first
            | (have i₁ := b4e26590 y
               have i₂ := b4e110020
               grind)
            | exact superpose b4e110020 b4e26590
            | exact resolve b4e26590 b4e110020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26590
          have b4e112022 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b4e111967
               have i₂ := b4e110020
               grind)
            | exact superpose b4e110020 b4e111967
            | exact resolve b4e111967 b4e110020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111967
          have b4e112049 : (M.op y (M.op (σ (M.op y y)) y)) = (M.op (σ x) (M.op y (M.op (σ (M.op y y)) y))) := by
            first
            | (have i₁ := b4e111849
               have i₂ := b4e2777
               grind)
            | exact superpose b4e2777 b4e111849
            | exact resolve b4e111849 b4e2777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2777 b4e111849
          have b4e112110 : (M.op y (M.op (σ y) y)) = (M.op (σ x) (M.op y (M.op (σ y) y))) := by
            first
            | (have i₁ := b4e112049
               have i₂ := b4e110020
               grind)
            | exact superpose b4e110020 b4e112049
            | exact resolve b4e112049 b4e110020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112049
          have b4e112126 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b4e112110
               have i₂ := b4e111953 y
               grind)
            | exact superpose b4e111953 b4e112110
            | exact resolve b4e112110 b4e111953
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111953 b4e112110
          have b4e112134 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e112126
               have i₂ := b4e110020
               grind)
            | exact superpose b4e110020 b4e112126
            | exact resolve b4e112126 b4e110020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110020 b4e112126
          have b4e124040 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e112134
               grind)
            | exact superpose b4e112134 b4e20
            | exact resolve b4e20 b4e112134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112134
          have b4e124049 : False := by grind
          exact b4e124049
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : (M.op y y) = (M.op x x) := by grind
          have b5e24 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e90 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X1 ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X1 X2
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e17 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X1 X2
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X1 X0
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 (M.op X1 X1) X1
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e6812 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e90 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e6813 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e6812 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6812
          have b5e13739 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          clear b5e6813
          have b5e13983 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e13739 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13739
          have b5e14104 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e13983 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13983
          have b5e14508 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e14104 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14104
          have b5e14976 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e14508 (σ X0)
               grind)
            | exact superpose b5e14508 b5e19
            | exact resolve b5e19 b5e14508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e14997 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e14976 X0
               have i₂ := b5e14508 X0
               grind)
            | exact superpose b5e14508 b5e14976
            | exact resolve b5e14976 b5e14508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14508 b5e14976
          have b5e16110 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e14997 x
               grind)
            | exact superpose b5e14997 b5e24
            | exact resolve b5e24 b5e14997
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16261 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e16110
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16110
            | exact resolve b5e16110 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16110
          have b5e16285 : False := by grind
          exact b5e16285
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : (M.op y y) ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e35 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e37 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e35
          | exact resolve b6e35 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e52 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e37
             grind)
          | exact superpose b6e37 b6e19
          | exact resolve b6e19 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e85 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e52
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e52 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e86 : (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by grind
        clear b6e85
        have b6e87 : x = (M.op y y) := by
          first
          | (have r₁ := b6e86
             have r₂ := b6e21
             grind)
          | exact resolve b6e86 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e88 : False := by grind
        exact b6e88
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : (M.op y y) ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e90 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X1 ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X1 X2
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e17 X1 X1
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e17
            | (have j0 := b7e17 X1 X2
               have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e17 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X1 X0
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X1 X1
               have r₂ := b7e18 (M.op X1 X1) X1
               grind)
            | exact resolve b7e17 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e126 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e61 (σ X0)
               grind)
            | exact superpose b7e61 b7e19
            | (have j1 := b7e61 (σ X0)
               grind)
            | exact resolve b7e19 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e927 : (M.op (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e126 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e126
            | exact resolve b7e126 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e980 : (M.op (σ y) (σ y)) = (σ (k x x)) := by
            first
            | (have r₁ := b7e927
               have r₂ := b7e23
               grind)
            | exact resolve b7e927 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e927
          have b7e1176 : (σ (k x x)) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e126 y
               have i₂ := b7e980
               grind)
            | exact superpose b7e980 b7e126
            | exact resolve b7e126 b7e980
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126
          have b7e5326 : (k x x) = (τ (σ (k y y))) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e1176
               grind)
            | exact superpose b7e1176 b7e14
            | exact resolve b7e14 b7e1176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1176
          have b7e5365 : (σ y) = (σ (k x x)) ∨ (k x x) = (k y y) := by
            first
            | (have i₁ := b7e5326
               have i₂ := b7e14 (k y y)
               grind)
            | exact superpose b7e14 b7e5326
            | exact resolve b7e5326 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5326
          have b7e7593 : (k x x) = (τ (σ y)) ∨ (k x x) = (k y y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e5365
               grind)
            | exact superpose b7e5365 b7e14
            | exact resolve b7e14 b7e5365
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5365
          have b7e7637 : (k x x) = (k y y) ∨ y = (k x x) := by
            first
            | (have i₁ := b7e7593
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e7593
            | exact resolve b7e7593 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7593
          have b7e7736 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e90 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e7737 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e7736 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7736
          have b7e14163 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          clear b7e7737
          have b7e14396 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e14163 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14163
          have b7e14456 : (M.op x x) = (k y y) ∨ (M.op x x) = (k y y) ∨ y = (k x x) := by
            first
            | (have i₁ := b7e14396 x x
               have i₂ := b7e7637
               grind)
            | exact superpose b7e7637 b7e14396
            | exact resolve b7e14396 b7e7637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7637
          have b7e14524 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e14396 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e14526 : y = (k x x) ∨ (M.op x x) = (k y y) := by grind
          clear b7e14456
          have b7e14853 : y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x x) = (k y y) := by
            first
            | (have i₁ := b7e14396 x x
               have i₂ := b7e14526
               grind)
            | exact superpose b7e14526 b7e14396
            | exact resolve b7e14396 b7e14526
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14526
          have b7e14854 : (M.op x x) = (k y y) ∨ y = (M.op x x) := by grind
          clear b7e14853
          have b7e15269 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e14396 y y
               have i₂ := b7e14854
               grind)
            | exact superpose b7e14854 b7e14396
            | exact resolve b7e14396 b7e14854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14396 b7e14854
          have b7e15270 : (M.op y y) = (M.op x x) ∨ y = (M.op x x) := by grind
          clear b7e15269
          have b7e15276 : y = (M.op x x) := by
            first
            | (have r₁ := b7e15270
               have r₂ := b7e22
               grind)
            | exact resolve b7e15270 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e15270
          have b7e15589 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e15276
               grind)
            | exact superpose b7e15276 b7e22
            | exact resolve b7e22 b7e15276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27582 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (k x x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e14524 (σ y) (σ y)
               have i₂ := b7e980
               grind)
            | exact superpose b7e980 b7e14524
            | exact resolve b7e14524 b7e980
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e980
          have b7e27584 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e14524 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14524
          have b7e27586 : (σ (k x x)) = (k (σ y) (σ y)) := by grind
          clear b7e27582
          have b7e27702 : (σ (k x x)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e27586
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e27586
            | exact resolve b7e27586 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27586
          have b7e27791 : (σ (k x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e27702
               have i₂ := b7e27584 y
               grind)
            | exact superpose b7e27584 b7e27702
            | exact resolve b7e27702 b7e27584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27702
          have b7e27822 : (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e27791
               have i₂ := b7e27584 x
               grind)
            | exact superpose b7e27584 b7e27791
            | exact resolve b7e27791 b7e27584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27584 b7e27791
          have b7e27840 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e27822
               have i₂ := b7e15276
               grind)
            | exact superpose b7e15276 b7e27822
            | exact resolve b7e27822 b7e15276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e15276 b7e27822
          have b7e30018 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e27840
               grind)
            | exact superpose b7e27840 b7e14
            | exact resolve b7e14 b7e27840
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27840
          have b7e30060 : y = (M.op y y) := by
            first
            | (have i₁ := b7e30018
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e30018
            | exact resolve b7e30018 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30018
          have b7e30071 : False := by grind
          exact b7e30071
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : (M.op y y) ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e89 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ x)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (M.op (σ x) (σ x)) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e90 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (k x X0) = (M.op x X0) ∨ (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b8e22
               have i₂ := b8e18 x X0
               grind)
            | (have i₁ := b8e22
               have i₂ := b8e18 X0 x
               grind)
            | exact superpose b8e18 b8e22
            | (have j1 := b8e18 x X0
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 (M.op x x) y
               grind)
            | exact resolve b8e22 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e351 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
            first
            | (have j0 := b8e90 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e352 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e351
               have r₂ := b8e21
               grind)
            | exact resolve b8e351 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e351
          have b8e1557 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have j0 := b8e89 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e1558 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1557
               have r₂ := b8e23
               grind)
            | exact resolve b8e1557 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1557
          have b8e1560 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1558
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1558
            | exact resolve b8e1558 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1558
          have b8e1561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1560
               have i₂ := b8e352
               grind)
            | exact superpose b8e352 b8e1560
            | exact resolve b8e1560 b8e352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e352 b8e1560
          have b8e1562 : False := by grind
          exact b8e1562

/-- `Equation3545`: `x ◇ y = y ◇ ((x ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation3545 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3545 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3545.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e45 : (M.op x y) = (k x y) := by grind
      have b0e46 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e51 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e46
        | exact resolve b0e46 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e54 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e51
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e51
        | exact resolve b0e51 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e51
      have b0e56 : False := by grind
      exact b0e56
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b1e12 y X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : (M.op x y) = (k x y) := by grind
        have b1e44 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
        have b1e49 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e44
          | exact resolve b1e44 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e55 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e57 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b1e59 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e55
             have r₂ := b1e21
             grind)
          | exact resolve b1e55 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e62 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e59
          | exact resolve b1e59 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e65 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e62
          | exact resolve b1e62 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e62
        have b1e70 : (M.op x y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op x y)
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e13
          | exact resolve b1e13 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e71 : x = (M.op x y) := by
          first
          | (have i₁ := b1e70
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e70
          | exact resolve b1e70 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b1e130 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e27 X0
             have i₂ := b1e71
             grind)
          | exact superpose b1e71 b1e27
          | exact resolve b1e27 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e71
        have b1e137 : (M.op (M.op y x) x) = (k (M.op y x) x) := by grind
        have b1e142 : (M.op (M.op y y) x) = (k (M.op y y) x) := by
          first
          | (have i₁ := b1e137
             have i₂ := b1e130 y
             grind)
          | exact superpose b1e130 b1e137
          | exact resolve b1e137 b1e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e137
        have b1e146 : (M.op x x) = (k x x) := by
          first
          | (have i₁ := b1e142
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e142
          | exact resolve b1e142 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e142
        have b1e150 : (M.op y x) = (k x x) := by
          first
          | (have i₁ := b1e146
             have i₂ := b1e130 x
             grind)
          | exact superpose b1e130 b1e146
          | exact resolve b1e146 b1e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e146
        have b1e154 : (M.op y y) = (k x x) := by
          first
          | (have i₁ := b1e150
             have i₂ := b1e130 y
             grind)
          | exact superpose b1e130 b1e150
          | exact resolve b1e150 b1e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e150
        have b1e158 : x = (k x x) := by
          first
          | (have i₁ := b1e154
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e154
          | exact resolve b1e154 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e154
        have b1e892 : (M.op y x) = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e57 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e57
          | exact resolve b1e57 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e895 : (M.op y y) = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e892
             have i₂ := b1e130 y
             grind)
          | exact superpose b1e130 b1e892
          | exact resolve b1e892 b1e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e130 b1e892
        have b1e905 : x = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e895
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e895
          | exact resolve b1e895 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e895
        have b1e1101 : x ≠ y ∨ y = (k y x) := by grind
        clear b1e905
        have b1e3791 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e104 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e104
          | exact resolve b1e104 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104
        have b1e4014 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b1e3791
        have b1e4073 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e4014
             have i₂ := b1e158
             grind)
          | exact superpose b1e158 b1e4014
          | exact resolve b1e4014 b1e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e158 b1e4014
        have b1e4074 : (σ x) = (σ y) := by grind
        clear b1e4073
        have b1e4170 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e4074
             grind)
          | exact superpose b1e4074 b1e19
          | exact resolve b1e19 b1e4074
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4173 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e4074
             grind)
          | exact superpose b1e4074 b1e49
          | exact resolve b1e49 b1e4074
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e4180 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e4074
             grind)
          | exact superpose b1e4074 b1e13
          | exact resolve b1e13 b1e4074
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4182 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 x
             have i₂ := b1e4074
             grind)
          | exact superpose b1e4074 b1e18
          | exact resolve b1e18 b1e4074
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4191 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e4182 X0
             have i₂ := b1e18 X0 y
             grind)
          | exact superpose b1e18 b1e4182
          | exact resolve b1e4182 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4182
        have b1e4193 : x = y := by
          first
          | (have i₁ := b1e4180
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e4180
          | exact resolve b1e4180 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4180
        have b1e4197 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e4170
             have i₂ := b1e4173
             grind)
          | exact superpose b1e4173 b1e4170
          | exact resolve b1e4170 b1e4173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4170 b1e4173
        have b1e4199 : (σ (M.op x y)) ≠ (σ (k y y)) := by
          first
          | (have i₁ := b1e4197
             have i₂ := b1e4191 y
             grind)
          | exact superpose b1e4191 b1e4197
          | exact resolve b1e4197 b1e4191
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4191 b1e4197
        have b1e4200 : (σ x) ≠ (σ (k y y)) := by
          first
          | (have i₁ := b1e4199
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e4199
          | exact resolve b1e4199 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e4199
        have b1e4201 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have i₁ := b1e4200
             have i₂ := b1e4074
             grind)
          | exact superpose b1e4074 b1e4200
          | exact resolve b1e4200 b1e4074
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4074 b1e4200
        have b1e4661 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e1101
             have i₂ := b1e4193
             grind)
          | exact superpose b1e4193 b1e1101
          | (have r₁ := b1e1101
             have r₂ := b1e4193
             grind)
          | exact resolve b1e1101 b1e4193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1101 b1e4193
        have b1e4662 : y = (k y y) := by grind
        clear b1e4661
        have b1e5931 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e4201
             have i₂ := b1e4662
             grind)
          | exact superpose b1e4662 b1e4201
          | exact resolve b1e4201 b1e4662
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4201 b1e4662
        have b1e5943 : False := by grind
        exact b1e5943
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e29 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op (M.op X0 X0) X0) X1
             have i₂ := b2e12 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e29 X0 X1
             have i₂ := b2e12 X0 (M.op (M.op X0 X0) X0)
             grind)
          | exact superpose b2e12 b2e29
          | exact resolve b2e29 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e32 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e30 X0 X1
             have i₂ := b2e12 X0 X0
             grind)
          | exact superpose b2e12 b2e30
          | exact resolve b2e30 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e53 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b2e54 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) X1) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          grind
        have b2e80 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ x)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (M.op (σ x) (σ x)) x
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e82 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b2e143 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X1 X1) X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 (M.op (M.op X1 X1) X1)
             have i₂ := b2e32 X1 (M.op X0 (M.op X0 X0))
             grind)
          | exact superpose b2e32 b2e32
          | exact resolve b2e32 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e159 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e143 X0 X1
             have i₂ := b2e12 X1 (M.op (M.op X0 X0) X0)
             grind)
          | exact superpose b2e12 b2e143
          | exact resolve b2e143 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e143
        have b2e175 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e159 X0 X1
             have i₂ := b2e12 X0 X1
             grind)
          | exact superpose b2e12 b2e159
          | exact resolve b2e159 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159
        have b2e444 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e53 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e579 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have j0 := b2e80 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e580 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b2e579
             have r₂ := b2e21
             grind)
          | exact resolve b2e579 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e579
        have b2e581 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e580
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e580
          | exact resolve b2e580 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e580
        have b2e582 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e581
             grind)
          | exact superpose b2e581 b2e19
          | exact resolve b2e19 b2e581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e581
        have b2e647 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e82 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e648 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e647 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e647
        have b2e747 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X1)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X1 (M.op X0 (M.op X0 X0))
             have i₂ := b2e54 X0 (M.op (M.op X1 X1) X1)
             grind)
          | exact superpose b2e54 b2e32
          | (have j1 := b2e54 X0 X1
             grind)
          | exact resolve b2e32 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e54
        have b2e748 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e747 X0 X1
             have i₂ := b2e12 X1 (M.op X0 X0)
             grind)
          | exact superpose b2e12 b2e747
          | (have j0 := b2e747 X0 X1
             grind)
          | exact resolve b2e747 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e747
        have b2e764 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e748 X0 X1
             have i₂ := b2e175 X0 X1
             grind)
          | exact superpose b2e175 b2e748
          | (have j0 := b2e748 X0 X1
             grind)
          | exact resolve b2e748 b2e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e175 b2e748
        have b2e1665 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e89 y y
             grind)
          | exact superpose b2e89 b2e21
          | (have j1 := b2e89 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e89 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e89 x y
             grind)
          | exact resolve b2e21 b2e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e1778 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e1665
        have b2e5585 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e1778
             have i₂ := b2e648 y
             grind)
          | exact superpose b2e648 b2e1778
          | (have j1 := b2e648 (σ y)
             grind)
          | exact resolve b2e1778 b2e648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1778
        have b2e5588 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e5585
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5585
          | exact resolve b2e5585 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5585
        have b2e5589 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e5588
        have b2e5606 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e5589
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5589
          | exact resolve b2e5589 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5589
        have b2e5637 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e5606
             grind)
          | exact superpose b2e5606 b2e21
          | exact resolve b2e21 b2e5606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5675 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e444 (σ y)
             have i₂ := b2e5606
             grind)
          | exact superpose b2e5606 b2e444
          | exact resolve b2e444 b2e5606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5677 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
          first
          | (have r₁ := b2e5675
             have r₂ := b2e5606
             grind)
          | exact resolve b2e5675 b2e5606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5606 b2e5675
        have b2e5689 : (σ y) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b2e5677
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e5677
          | exact resolve b2e5677 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5677
        have b2e5873 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        clear b2e764
        have b2e5890 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e5873 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5873
        have b2e5901 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e5890 X0
             have j1 := b2e444 X0
             grind)
          | (have r₁ := b2e5890 X0
             have r₂ := b2e444 X0
             grind)
          | exact resolve b2e5890 b2e444
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e444 b2e5890
        have b2e5999 : y = (k y x) := by
          first
          | (have i₁ := b2e5901 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5901
          | exact resolve b2e5901 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5901
        have b2e6090 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e582
             have i₂ := b2e5999
             grind)
          | exact superpose b2e5999 b2e582
          | exact resolve b2e582 b2e5999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e582 b2e5999
        have b2e7066 : (σ y) = (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e5689
             have i₂ := b2e648 y
             grind)
          | exact superpose b2e648 b2e5689
          | (have j1 := b2e648 y
             grind)
          | exact resolve b2e5689 b2e648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e648 b2e5689
        have b2e7102 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e7066
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e7066
          | exact resolve b2e7066 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7066
        have b2e7113 : x = y ∨ y = (M.op y y) := by
          first
          | (have r₁ := b2e7102
             have r₂ := b2e5637
             grind)
          | exact resolve b2e7102 b2e5637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5637 b2e7102
        have b2e7123 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e7113
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e7113
          | exact resolve b2e7113 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7113
        have b2e7124 : x = y := by grind
        clear b2e7123
        have b2e7342 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e6090
             have i₂ := b2e7124
             grind)
          | exact superpose b2e7124 b2e6090
          | exact resolve b2e6090 b2e7124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6090
        have b2e7344 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e7342
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e7342
          | exact resolve b2e7342 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7342
        have b2e7368 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e7344
             have i₂ := b2e7124
             grind)
          | exact superpose b2e7124 b2e7344
          | exact resolve b2e7344 b2e7124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7124 b2e7344
        have b2e7369 : False := by grind
        exact b2e7369
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e49 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e44
          | exact resolve b3e44 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e56 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e59 : x = (k x y) := by
          first
          | (have r₁ := b3e56
             have r₂ := b3e20
             grind)
          | exact resolve b3e56 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e135 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e28 X0
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e28
          | exact resolve b3e28 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e141 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by grind
        clear b3e28
        have b3e146 : (M.op (M.op (σ y) (σ (k x y))) (σ (k x y))) = (k (M.op (σ y) (σ (k x y))) (σ (k x y))) := by
          first
          | (have i₁ := b3e141
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e141
          | exact resolve b3e141 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141
        have b3e152 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e135 X0
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e135
          | exact resolve b3e135 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135
        have b3e155 : (M.op (M.op (σ y) (σ x)) (σ x)) = (k (M.op (σ y) (σ x)) (σ x)) := by
          first
          | (have i₁ := b3e146
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e146
          | exact resolve b3e146 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e146
        have b3e163 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (σ y) (σ y)) (σ x)) := by
          first
          | (have i₁ := b3e155
             have i₂ := b3e152 (σ y)
             grind)
          | exact superpose b3e152 b3e155
          | exact resolve b3e155 b3e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e155
        have b3e171 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e163
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e163
          | exact resolve b3e163 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e163
        have b3e179 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e171
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e171
          | exact resolve b3e171 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e187 : (M.op (σ y) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e179
             have i₂ := b3e152 (σ x)
             grind)
          | exact superpose b3e152 b3e179
          | exact resolve b3e179 b3e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e179
        have b3e195 : (M.op (σ y) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e187
             have i₂ := b3e152 (σ y)
             grind)
          | exact superpose b3e152 b3e187
          | exact resolve b3e187 b3e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152 b3e187
        have b3e196 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e195
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e195
          | exact resolve b3e195 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e195
        have b3e200 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e196
             grind)
          | exact superpose b3e196 b3e13
          | exact resolve b3e13 b3e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196
        have b3e202 : x = (k x x) := by
          first
          | (have i₁ := b3e200
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e200
          | exact resolve b3e200 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e200
        have b3e301 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e202
             grind)
          | exact superpose b3e202 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e302 : x = (M.op x x) := by grind
        clear b3e301
        have b3e304 : x = y := by
          first
          | (have i₁ := b3e302
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e302
          | exact resolve b3e302 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e302
        have b3e362 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e304
             grind)
          | exact superpose b3e304 b3e19
          | exact resolve b3e19 b3e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e363 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e304
             grind)
          | exact superpose b3e304 b3e21
          | exact resolve b3e21 b3e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e367 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e49
             have i₂ := b3e304
             grind)
          | exact superpose b3e304 b3e49
          | exact resolve b3e49 b3e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e372 : y = (k y y) := by
          first
          | (have i₁ := b3e202
             have i₂ := b3e304
             grind)
          | exact superpose b3e304 b3e202
          | exact resolve b3e202 b3e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e202 b3e304
        have b3e373 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e367
             have i₂ := b3e372
             grind)
          | exact superpose b3e372 b3e367
          | exact resolve b3e367 b3e372
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e367 b3e372
        have b3e376 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e362
             have i₂ := b3e363
             grind)
          | exact superpose b3e363 b3e362
          | exact resolve b3e362 b3e363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e362 b3e363
        have b3e377 : False := by grind
        exact b3e377
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
            intro X0 X1
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e33 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : (M.op y x) = (k y x) := by grind
          have b4e50 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
          have b4e52 : (M.op (M.op x (M.op y x)) (M.op y x)) = (k (M.op x (M.op y x)) (M.op y x)) := by grind
          have b4e53 : (M.op (M.op x x) (M.op y x)) = (k (M.op x x) (M.op y x)) := by
            first
            | (have i₁ := b4e52
               have i₂ := b4e33 x
               grind)
            | exact superpose b4e33 b4e52
            | exact resolve b4e52 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e55 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e50
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e50
            | exact resolve b4e50 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e56 : (M.op y (M.op y x)) = (k y (M.op y x)) := by
            first
            | (have i₁ := b4e53
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e53
            | exact resolve b4e53 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e58 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e55
               have i₂ := b4e49
               grind)
            | exact superpose b4e49 b4e55
            | exact resolve b4e55 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e55
          have b4e59 : (M.op x y) = (k y (M.op y x)) := by
            first
            | (have i₁ := b4e56
               have i₂ := b4e33 y
               grind)
            | exact superpose b4e33 b4e56
            | exact resolve b4e56 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e56
          have b4e138 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e58
               grind)
            | exact superpose b4e58 b4e34
            | exact resolve b4e34 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e144 : (M.op (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ y) (σ x))) = (k (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ y) (σ x))) := by grind
          clear b4e34
          have b4e149 : (M.op (M.op (σ x) (σ (M.op y x))) (σ (M.op y x))) = (k (M.op (σ x) (σ (M.op y x))) (σ (M.op y x))) := by
            first
            | (have i₁ := b4e144
               have i₂ := b4e58
               grind)
            | exact superpose b4e58 b4e144
            | exact resolve b4e144 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58 b4e144
          have b4e157 : (M.op (M.op (σ x) (σ x)) (σ (M.op y x))) = (k (M.op (σ x) (σ x)) (σ (M.op y x))) := by
            first
            | (have i₁ := b4e149
               have i₂ := b4e138 (σ x)
               grind)
            | exact superpose b4e138 b4e149
            | exact resolve b4e149 b4e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149
          have b4e165 : (M.op (σ y) (σ (M.op y x))) = (k (σ y) (σ (M.op y x))) := by
            first
            | (have i₁ := b4e157
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e157
            | exact resolve b4e157 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e157
          have b4e173 : (M.op (σ y) (σ (M.op y x))) = (σ (k y (M.op y x))) := by
            first
            | (have i₁ := b4e165
               have i₂ := b4e19 y (M.op y x)
               grind)
            | exact superpose b4e19 b4e165
            | exact resolve b4e165 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e165
          have b4e179 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have i₁ := b4e173
               have i₂ := b4e59
               grind)
            | exact superpose b4e59 b4e173
            | exact resolve b4e173 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59 b4e173
          have b4e183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e179
               have i₂ := b4e138 (σ y)
               grind)
            | exact superpose b4e138 b4e179
            | exact resolve b4e179 b4e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138 b4e179
          have b4e185 : False := by grind
          exact b4e185
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e48 : (M.op y x) = (k y x) := by grind
          have b5e59 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b5e88 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
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
          have b5e90 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b5e97 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b5e461 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e59 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e612 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e88 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e613 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e612
               have r₂ := b5e23
               grind)
            | exact resolve b5e612 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e612
          have b5e614 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e613
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e613
            | exact resolve b5e613 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e613
          have b5e615 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e614
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e614
            | exact resolve b5e614 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e614
          have b5e616 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e615
               grind)
            | exact superpose b5e615 b5e20
            | exact resolve b5e20 b5e615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e615
          have b5e682 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e90 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e683 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e682 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e682
          have b5e1822 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e97 x x
               grind)
            | exact superpose b5e97 b5e24
            | (have j1 := b5e97 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e97 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e97 y x
               grind)
            | exact resolve b5e24 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97
          have b5e1945 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e1822
          have b5e4877 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1945
               have i₂ := b5e683 x
               grind)
            | exact superpose b5e683 b5e1945
            | (have j1 := b5e683 (σ x)
               grind)
            | exact resolve b5e1945 b5e683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1945
          have b5e4880 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e4877
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4877
            | exact resolve b5e4877 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4877
          have b5e4881 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e4880
          have b5e4898 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e4881
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4881
            | exact resolve b5e4881 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4881
          have b5e4972 : (σ x) ≠ (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e4898
               grind)
            | exact superpose b5e4898 b5e24
            | exact resolve b5e24 b5e4898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5010 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e461 (σ x)
               have i₂ := b5e4898
               grind)
            | exact superpose b5e4898 b5e461
            | exact resolve b5e461 b5e4898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e461
          have b5e5012 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
            first
            | (have r₁ := b5e5010
               have r₂ := b5e4898
               grind)
            | exact resolve b5e5010 b5e4898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4898 b5e5010
          have b5e5023 : (σ x) = (σ (k x x)) ∨ x = y := by
            first
            | (have i₁ := b5e5012
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e5012
            | exact resolve b5e5012 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5012
          have b5e5817 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e5023
               have i₂ := b5e683 x
               grind)
            | exact superpose b5e683 b5e5023
            | (have j1 := b5e683 x
               grind)
            | exact resolve b5e5023 b5e683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e683 b5e5023
          have b5e5853 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e5817
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e5817
            | exact resolve b5e5817 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5817
          have b5e5864 : x = y ∨ x = (M.op x x) := by
            first
            | (have r₁ := b5e5853
               have r₂ := b5e4972
               grind)
            | exact resolve b5e5853 b5e4972
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4972 b5e5853
          have b5e5874 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e5864
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e5864
            | exact resolve b5e5864 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5864
          have b5e5875 : x = y := by grind
          clear b5e5874
          have b5e6403 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e616
               have i₂ := b5e5875
               grind)
            | exact superpose b5e5875 b5e616
            | exact resolve b5e616 b5e5875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e616 b5e5875
          have b5e6407 : False := by grind
          exact b5e6407
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e38 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e41 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e38
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e38
          | exact resolve b6e38 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e59 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e19
          | exact resolve b6e19 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e72 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (k x y) = (M.op y x) := by
          first
          | (have i₁ := b6e59
             have i₂ := b6e72 x y
             grind)
          | exact superpose b6e72 b6e59
          | (have j1 := b6e72 x y
             grind)
          | exact resolve b6e59 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e72
        have b6e682 : y = (M.op x x) ∨ (k x y) = (M.op y x) := by grind
        clear b6e651
        have b6e693 : (k x y) = (M.op y x) := by
          first
          | (have r₁ := b6e682
             have r₂ := b6e21
             grind)
          | exact resolve b6e682 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e682
        have b6e2230 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e84 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e84
          | exact resolve b6e84 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e2449 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e2230
        have b6e2667 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e2449
             grind)
          | exact superpose b6e2449 b6e13
          | exact resolve b6e13 b6e2449
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2449
        have b6e2681 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2667
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2667
          | exact resolve b6e2667 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2667
        have b6e3009 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e78 y y
             have i₂ := b6e2681
             grind)
          | exact superpose b6e2681 b6e78
          | (have j0 := b6e78 y x
             grind)
          | exact resolve b6e78 b6e2681
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e3013 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e3009
        have b6e3022 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3013
             have r₂ := b6e20
             grind)
          | exact resolve b6e3013 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3013
        have b6e3322 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by grind
        clear b6e3022
        have b6e3826 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2681
             have i₂ := b6e3322
             grind)
          | exact superpose b6e3322 b6e2681
          | exact resolve b6e2681 b6e3322
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2681 b6e3322
        have b6e3829 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e3826
        have b6e3831 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3829
             have r₂ := b6e20
             grind)
          | exact resolve b6e3829 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3829
        have b6e4461 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e3831
             grind)
          | exact superpose b6e3831 b6e19
          | exact resolve b6e19 b6e3831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4463 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e3831
             grind)
          | exact superpose b6e3831 b6e41
          | exact resolve b6e41 b6e3831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e4468 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e3831
             grind)
          | exact superpose b6e3831 b6e13
          | exact resolve b6e13 b6e3831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4485 : x = y := by
          first
          | (have i₁ := b6e4468
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e4468
          | exact resolve b6e4468 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4468
        have b6e4490 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e4463
             have i₂ := b6e693
             grind)
          | exact superpose b6e693 b6e4463
          | exact resolve b6e4463 b6e693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e693 b6e4463
        have b6e4492 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4461
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4461
          | exact resolve b6e4461 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4461
        have b6e4500 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e4490
             have i₂ := b6e4485
             grind)
          | exact superpose b6e4485 b6e4490
          | exact resolve b6e4490 b6e4485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4490
        have b6e4502 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e4492
             have i₂ := b6e3831
             grind)
          | exact superpose b6e3831 b6e4492
          | exact resolve b6e4492 b6e3831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4492
        have b6e4510 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e4500
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4500
          | exact resolve b6e4500 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4500
        have b6e4511 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e4502
             have i₂ := b6e4485
             grind)
          | exact superpose b6e4485 b6e4502
          | exact resolve b6e4502 b6e4485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4485 b6e4502
        have b6e4513 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e4510
             have i₂ := b6e3831
             grind)
          | exact superpose b6e3831 b6e4510
          | exact resolve b6e4510 b6e3831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3831 b6e4510
        have b6e4514 : False := by grind
        exact b6e4514
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e56 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b7e87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e444 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e56 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e2576 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e94 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e94
            | exact resolve b7e94 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e2805 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e2576
          have b7e3057 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e2805
               grind)
            | exact superpose b7e2805 b7e14
            | exact resolve b7e14 b7e2805
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3071 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3057
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e3057
            | exact resolve b7e3057 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3057
          have b7e3419 : y = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e87 x x
               have i₂ := b7e3071
               grind)
            | exact superpose b7e3071 b7e87
            | (have j0 := b7e87 x y
               grind)
            | exact resolve b7e87 b7e3071
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87 b7e3071
          have b7e3423 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
          clear b7e3419
          have b7e3432 : x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3423
               have r₂ := b7e22
               grind)
            | exact resolve b7e3423 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3423
          have b7e3764 : x ≠ (M.op x x) ∨ x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e444 x
               have i₂ := b7e3432
               grind)
            | exact superpose b7e3432 b7e444
            | exact resolve b7e444 b7e3432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e444
          have b7e3765 : x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3764
               have r₂ := b7e3432
               grind)
            | exact resolve b7e3764 b7e3432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3432 b7e3764
          have b7e4327 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2805
               have i₂ := b7e3765
               grind)
            | exact superpose b7e3765 b7e2805
            | exact resolve b7e2805 b7e3765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2805 b7e3765
          have b7e4352 : (σ x) = (σ y) := by grind
          clear b7e4327
          have b7e5131 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e4352
               grind)
            | exact superpose b7e4352 b7e23
            | exact resolve b7e23 b7e4352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e5162 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e5131
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e5131
            | exact resolve b7e5131 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5131
          have b7e5174 : False := by grind
          exact b7e5174
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e92 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
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
          have b8e527 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e92 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e528 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e527
               have r₂ := b8e23
               grind)
            | exact resolve b8e527 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e527
          have b8e529 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e528
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e528
            | exact resolve b8e528 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e528
          have b8e530 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e529
               grind)
            | exact superpose b8e529 b8e20
            | exact resolve b8e20 b8e529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e529
          have b8e647 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e530
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e530
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e530 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e530
          have b8e657 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e647
          have b8e664 : x = (M.op y y) := by
            first
            | (have r₁ := b8e657
               have r₂ := b8e22
               grind)
            | exact resolve b8e657 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e657
          have b8e668 : False := by grind
          exact b8e668
