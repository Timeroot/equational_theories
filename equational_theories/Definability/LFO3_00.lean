import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),m(X,Y)) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxpxy_y_x_y_pxy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 1))) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 1))) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) (M.op a b) ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a b)) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) (M.op a b) = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a b)) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) (M.op a b) = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a b)) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) (M.op x y)) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op (M.op x x) (M.op x y)) := by grind
      have b0e20 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
      have b0e31 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e32 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e31
      have b0e33 : (M.op x y) = (k x y) := by grind
      clear b0e30
      have b0e34 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
      have b0e35 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e34
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e34
        | exact resolve b0e34 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e34
      have b0e36 : False := by grind
      exact b0e36
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e61 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b1e65 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e61 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e65 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e66 (σ X0)
             grind)
          | exact superpose b1e66 b1e18
          | exact resolve b1e18 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e70 X0
             have i₂ := b1e66 X0
             grind)
          | exact superpose b1e66 b1e70
          | exact resolve b1e70 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e70
        have b1e149 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e73 x
             grind)
          | exact superpose b1e73 b1e25
          | exact resolve b1e25 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e73
        have b1e160 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
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
        have b1e161 : False := by grind
        exact b1e161
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op (M.op x x) (M.op x y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e39 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
        have b2e40 : (M.op x y) = (k x y) := by grind
        clear b2e39
        have b2e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 (k X1 X0) (M.op X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op (M.op X0 X0) (M.op X0 X1)) X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e64 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e64 (σ X1) (σ X0)
             grind)
          | exact superpose b2e64 b2e18
          | (have j1 := b2e64 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e513 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
        have b2e523 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e513
             have r₂ := b2e22
             grind)
          | exact resolve b2e513 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e513
        have b2e530 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e523
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e523
          | exact resolve b2e523 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e523
        have b2e531 : False := by grind
        exact b2e531
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e35 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e36 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b3e35
        have b3e38 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e36
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e36
          | exact resolve b3e36 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e48 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b3e52 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e48 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e74 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e38
        have b3e80 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e74
             have i₂ := b3e53 y
             grind)
          | exact superpose b3e53 b3e74
          | exact resolve b3e74 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e74
        have b3e81 : False := by grind
        exact b3e81
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e46 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            grind
          have b4e50 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e50 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e51 (σ X0)
               grind)
            | exact superpose b4e51 b4e19
            | exact resolve b4e19 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e55 X0
               have i₂ := b4e51 X0
               grind)
            | exact superpose b4e51 b4e55
            | exact resolve b4e55 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e55
          have b4e124 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
          clear b4e60
          have b4e132 : False := by grind
          exact b4e132
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ((σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e39 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e39
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
        have b6e43 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b6e66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 (k X1 X0) (M.op X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op (M.op X0 X0) (M.op X0 X1)) X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e68 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e66 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e69 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e68 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e81 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e69 y x
             grind)
          | exact superpose b6e69 b6e43
          | (have j1 := b6e69 x y
             grind)
          | (have r₁ := b6e43
             have r₂ := b6e69 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e43
             have r₂ := b6e69 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e43 b6e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e69
        have b6e82 : x = y := by grind
        clear b6e81
        have b6e83 : False := by grind
        exact b6e83
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
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e60 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 (k X1 X0) (M.op X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X0) (M.op X0 X1)) X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e63 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e63 (σ X1) (σ X0)
               grind)
            | exact superpose b8e63 b8e19
            | (have j1 := b8e63 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e63 X1 (τ X0)
               grind)
            | exact superpose b8e63 b8e26
            | (have j1 := b8e63 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e63
          have b8e165 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e68 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e68
            | exact resolve b8e68 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e165 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e165
            | (have j0 := b8e165 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e165 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165
          have b8e500 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
          have b8e510 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e500
               have r₂ := b8e24
               grind)
            | exact resolve b8e500 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e500
          have b8e521 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e510
               have i₂ := b8e181 x y
               grind)
            | exact superpose b8e181 b8e510
            | (have j1 := b8e181 x y
               grind)
            | (have r₁ := b8e510
               have r₂ := b8e181 x y
               grind)
            | (have r₁ := b8e510
               have r₂ := b8e181 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e510
               have r₂ := b8e181 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e510 b8e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181 b8e510
          have b8e522 : x = y := by grind
          clear b8e521
          have b8e524 : False := by grind
          exact b8e524

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),m(Y,Y)) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxpyy_y_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) (M.op b b) ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op b b)) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) (M.op b b) = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op b b)) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) (M.op b b) = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op b b)) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) (M.op y y)) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op (M.op x x) (M.op y y)) := by grind
      have b0e20 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
      have b0e28 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e29 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e28
      have b0e30 : (M.op x y) = (k x y) := by grind
      clear b0e27
      have b0e31 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e29
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e29
        | exact resolve b0e29 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e32 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e31
           have i₂ := b0e30
           grind)
        | exact superpose b0e30 b0e31
        | exact resolve b0e31 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e31
      have b0e33 : False := by grind
      exact b0e33
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op (M.op x x) (M.op y y)) := by grind
        have b1e21 : (σ y) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by grind
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
        have b1e38 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
        clear b1e38
        have b1e40 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e42 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e40
        have b1e43 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e42
             have r₂ := b1e21
             grind)
          | exact resolve b1e42 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e44 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e43
          | exact resolve b1e43 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e45 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e44
          | exact resolve b1e44 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e44
        have b1e46 : False := by grind
        exact b1e46
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op (M.op x x) (M.op y y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
        have b2e38 : (M.op x y) = (k x y) := by grind
        clear b2e37
        have b2e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
        have b2e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e56 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e323 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e75 x y
             grind)
          | exact superpose b2e75 b2e19
          | (have j1 := b2e75 x y
             grind)
          | exact resolve b2e19 b2e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e338 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e323
             have r₂ := b2e22
             grind)
          | exact resolve b2e323 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e323
        have b2e342 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e338
             have i₂ := b2e38
             grind)
          | exact superpose b2e38 b2e338
          | exact resolve b2e338 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e338
        have b2e343 : False := by grind
        exact b2e343
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op (M.op x x) (M.op y y)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by grind
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
        have b3e38 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e39 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e38
        have b3e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e39
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e39
          | exact resolve b3e39 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e41 : (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e23
          | exact resolve b3e23 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e40
        have b3e42 : y ≠ y ∨ y = (M.op (M.op x x) (M.op y y)) ∨ y = (k x y) := by
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
        have b3e45 : y = (M.op (M.op x x) (M.op y y)) ∨ y = (k x y) := by grind
        clear b3e42
        have b3e46 : y = (k x y) := by
          first
          | (have r₁ := b3e45
             have r₂ := b3e20
             grind)
          | exact resolve b3e45 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e59 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e46
             grind)
          | exact superpose b3e46 b3e41
          | exact resolve b3e41 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e46
        have b3e60 : False := by grind
        exact b3e60
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
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op (M.op x x) (M.op y y)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e48 : y ≠ y ∨ y = (M.op (M.op x x) (M.op y y)) ∨ y = (k x y) := by
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
          have b5e49 : y = (M.op (M.op x x) (M.op y y)) ∨ y = (k x y) := by grind
          clear b5e48
          have b5e50 : y = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
          have b5e59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e60 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e60 (σ X1) (σ X0)
               grind)
            | exact superpose b5e60 b5e19
            | (have j1 := b5e60 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e380 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e480 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e380 x y
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e380
            | (have j0 := b5e380 x y
               grind)
            | exact resolve b5e380 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e380
          have b5e484 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e480
          have b5e487 : False := by grind
          exact b5e487
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) ((σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e37 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e38 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e37
        have b6e39 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b6e40 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e39
             grind)
          | exact superpose b6e39 b6e19
          | exact resolve b6e19 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e46 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
        have b6e50 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e46 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e51 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e50 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e68 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e51 y x
             grind)
          | exact superpose b6e51 b6e40
          | (have j1 := b6e51 y x
             grind)
          | exact resolve b6e40 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e51
        have b6e69 : y = (M.op x y) := by grind
        clear b6e68
        have b6e70 : False := by grind
        exact b6e70
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e41 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e42 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e23
               grind)
            | exact resolve b7e41 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
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
          have b7e54 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
          have b7e58 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e59 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e69 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e59 y x
               grind)
            | exact superpose b7e59 b7e47
            | (have j1 := b7e59 y x
               grind)
            | exact resolve b7e47 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47 b7e59
          have b7e71 : y = (M.op x y) := by grind
          clear b7e69
          have b7e74 : False := by grind
          exact b7e74
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
          have b8e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e56 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e56 (σ X1) (σ X0)
               grind)
            | exact superpose b8e56 b8e19
            | (have j1 := b8e56 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e56 X1 (τ X0)
               grind)
            | exact superpose b8e56 b8e25
            | (have j1 := b8e56 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e56
          have b8e212 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e76 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e76
            | exact resolve b8e76 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e237 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e212 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e212
            | (have j0 := b8e212 X0 X1
               grind)
            | exact resolve b8e212 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212
          have b8e359 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e374 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e359
               have r₂ := b8e24
               grind)
            | exact resolve b8e359 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e359
          have b8e379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e374
               have i₂ := b8e237 x y
               grind)
            | exact superpose b8e237 b8e374
            | (have j1 := b8e237 x y
               grind)
            | (have r₁ := b8e374
               have r₂ := b8e237 x y
               grind)
            | exact resolve b8e374 b8e237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e237 b8e374
          have b8e380 : y = (M.op x y) := by grind
          clear b8e379
          have b8e382 : False := by grind
          exact b8e382

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),X) = m(m(Y,X),Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxx_ppyxy_x_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) a ≠ M.op (M.op b a) b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b a) b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) a = M.op (M.op b a) b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b a) b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) a = M.op (M.op b a) b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b a) b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) x) (M.op (M.op y x) y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ x)) (σ y)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X0) X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e75 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e14 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X0) X1)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e75 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e77 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e97 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e78 X1 (τ X0)
           grind)
        | exact superpose b0e78 b0e23
        | (have j1 := b0e78 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e98 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e78 (σ X1) (σ X0)
           grind)
        | exact superpose b0e78 b0e17
        | (have j1 := b0e78 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e209 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e97 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e97
        | exact resolve b0e97 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97
      have b0e225 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e209 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e209
        | (have j0 := b0e209 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e209 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e209
      have b0e566 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e98 x y
           grind)
        | exact superpose b0e98 b0e18
        | (have j1 := b0e98 x y
           grind)
        | exact resolve b0e18 b0e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98
      have b0e635 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e566
           have i₂ := b0e225 x y
           grind)
        | exact superpose b0e225 b0e566
        | (have j1 := b0e225 (σ x) (σ y)
           grind)
        | (have r₁ := b0e566
           have r₂ := b0e225 x y
           grind)
        | (have r₁ := b0e566
           have r₂ := b0e225 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e566
           have r₂ := b0e225 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e566 b0e225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e225 b0e566
      have b0e636 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e635
      have b0e643 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e636
           grind)
        | exact superpose b0e636 b0e12
        | exact resolve b0e12 b0e636
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e636
      have b0e674 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e643
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e643
        | exact resolve b0e643 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e643
      have b0e675 : x = y := by grind
      clear b0e674
      have b0e693 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e675
           grind)
        | exact superpose b0e675 b0e18
        | exact resolve b0e18 b0e675
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e675
      have b0e700 : False := by grind
      exact b0e700
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) := by
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
        have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X0) X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b2e60 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X0) X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e63 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
             have i₂ := b2e63 X1 (τ X0)
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
             have i₂ := b2e63 (σ X1) (σ X0)
             grind)
          | exact superpose b2e63 b2e18
          | (have j1 := b2e63 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e134 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
        have b2e150 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e134 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e134
          | (have j0 := b2e134 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b2e134 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134
        have b2e483 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
        have b2e497 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e483
             have r₂ := b2e22
             grind)
          | exact resolve b2e483 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e483
        have b2e507 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b2e497
             have i₂ := b2e150 x y
             grind)
          | exact superpose b2e150 b2e497
          | (have j1 := b2e150 x y
             grind)
          | (have r₁ := b2e497
             have r₂ := b2e150 x y
             grind)
          | (have r₁ := b2e497
             have r₂ := b2e150 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b2e497
             have r₂ := b2e150 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b2e497 b2e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150 b2e497
        have b2e508 : x = y := by grind
        clear b2e507
        have b2e561 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e508
             grind)
          | exact superpose b2e508 b2e22
          | exact resolve b2e22 b2e508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e508
        have b2e566 : False := by grind
        exact b2e566
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ x)) (σ y)) with h1a | h1a
      · have b3e20 : (M.op (M.op x x) x) ≠ (M.op (M.op y x) y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ x)) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X0) X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e61 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X0) X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e64 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e64 (σ X1) (σ X0)
             grind)
          | exact superpose b6e64 b6e18
          | (have j1 := b6e64 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b6e18 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e78 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X1 X0
             have i₂ := b6e64 (τ X1) X0
             grind)
          | exact superpose b6e64 b6e24
          | (have j1 := b6e64 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
             grind)
          | exact resolve b6e24 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e64
        have b6e163 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e78 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e78
          | exact resolve b6e78 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e163 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e163
          | (have j0 := b6e163 (σ (k X0 X1)) (σ (M.op X1 X0))
             grind)
          | exact resolve b6e163 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e163
        have b6e546 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e77 x y
             grind)
          | exact superpose b6e77 b6e19
          | (have j1 := b6e77 x y
             grind)
          | exact resolve b6e19 b6e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e609 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e546
             have i₂ := b6e181 y x
             grind)
          | exact superpose b6e181 b6e546
          | (have j1 := b6e181 (σ x) (σ y)
             grind)
          | (have r₁ := b6e546
             have r₂ := b6e181 y x
             grind)
          | (have r₁ := b6e546
             have r₂ := b6e181 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b6e546
             have r₂ := b6e181 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b6e546 b6e181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e181 b6e546
        have b6e610 : (σ x) = (σ y) ∨ x = y := by grind
        clear b6e609
        have b6e612 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e610
             have r₂ := b6e21
             grind)
          | exact resolve b6e610 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e610
        have b6e626 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e612
             grind)
          | exact superpose b6e612 b6e13
          | exact resolve b6e13 b6e612
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e612
        have b6e657 : x = y := by
          first
          | (have i₁ := b6e626
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e626
          | exact resolve b6e626 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e626
        have b6e660 : False := by grind
        exact b6e660
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) := by
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
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X0) X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e71 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X0) X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e74 (σ X1) (σ X0)
               grind)
            | exact superpose b8e74 b8e19
            | (have j1 := b8e74 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e74 (τ X1) X0
               grind)
            | exact superpose b8e74 b8e26
            | (have j1 := b8e74 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
               grind)
            | exact resolve b8e26 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e74
          have b8e128 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e80 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e80
            | exact resolve b8e80 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e128 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e128
            | (have j0 := b8e128 (σ (k X0 X1)) (σ (M.op X1 X0))
               grind)
            | exact resolve b8e128 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128
          have b8e473 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e79 x y
               grind)
            | exact superpose b8e79 b8e20
            | (have j1 := b8e79 x y
               grind)
            | exact resolve b8e20 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e487 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e473
               have r₂ := b8e24
               grind)
            | exact resolve b8e473 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e473
          have b8e496 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e487
               have i₂ := b8e146 y x
               grind)
            | exact superpose b8e146 b8e487
            | (have j1 := b8e146 x y
               grind)
            | (have r₁ := b8e487
               have r₂ := b8e146 y x
               grind)
            | (have r₁ := b8e487
               have r₂ := b8e146 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e487
               have r₂ := b8e146 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e487 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146 b8e487
          have b8e497 : x = y := by grind
          clear b8e496
          have b8e499 : False := by grind
          exact b8e499

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),X) = m(m(Y,Y),X) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxx_ppyyx_x_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) a ≠ M.op (M.op b b) a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b b) a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) a = M.op (M.op b b) a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b b) a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) a = M.op (M.op b b) a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b b) a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) x) (M.op (M.op y y) x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e46 (σ X0)
           grind)
        | exact superpose b0e46 b0e17
        | exact resolve b0e17 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e52 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e52
        | exact resolve b0e52 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e52
      have b0e68 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e14 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X1) X0)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e69 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e68 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e69 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e74 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e70 X1 (τ X0)
           grind)
        | exact superpose b0e70 b0e23
        | (have j1 := b0e70 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e70 (σ X1) (σ X0)
           grind)
        | exact superpose b0e70 b0e17
        | (have j1 := b0e70 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e133 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
      have b0e149 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e133 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e133
        | (have j0 := b0e133 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e133 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133
      have b0e471 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
      have b0e485 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e471
           have i₂ := b0e149 x y
           grind)
        | exact superpose b0e149 b0e471
        | (have j1 := b0e149 (σ x) (σ y)
           grind)
        | (have r₁ := b0e471
           have r₂ := b0e149 x y
           grind)
        | (have r₁ := b0e471
           have r₂ := b0e149 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e471
           have r₂ := b0e149 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e471 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149 b0e471
      have b0e486 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e485
      have b0e490 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e486
           grind)
        | exact superpose b0e486 b0e12
        | exact resolve b0e12 b0e486
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e486
      have b0e521 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e490
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e490
        | exact resolve b0e490 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e490
      have b0e522 : x = y := by grind
      clear b0e521
      have b0e575 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e522
           grind)
        | exact superpose b0e522 b0e18
        | exact resolve b0e18 b0e522
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e522
      have b0e578 : False := by grind
      exact b0e578
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) := by
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
        have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e54 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X1) X0)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e64 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e25 X0 X1
             have i₂ := b2e58 X1 (τ X0)
             grind)
          | exact superpose b2e58 b2e25
          | (have j1 := b2e58 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b2e25 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e58 (σ X1) (σ X0)
             grind)
          | exact superpose b2e58 b2e18
          | (have j1 := b2e58 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e120 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e64 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e64
          | exact resolve b2e64 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e120 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e120
          | (have j0 := b2e120 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b2e120 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120
        have b2e471 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e65 x y
             grind)
          | exact superpose b2e65 b2e19
          | (have j1 := b2e65 x y
             grind)
          | exact resolve b2e19 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e478 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e471
             have r₂ := b2e22
             grind)
          | exact resolve b2e471 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e471
        have b2e488 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b2e478
             have i₂ := b2e136 x y
             grind)
          | exact superpose b2e136 b2e478
          | (have j1 := b2e136 x y
             grind)
          | (have r₁ := b2e478
             have r₂ := b2e136 x y
             grind)
          | (have r₁ := b2e478
             have r₂ := b2e136 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b2e478
             have r₂ := b2e136 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b2e478 b2e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e136 b2e478
        have b2e489 : x = y := by grind
        clear b2e488
        have b2e542 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e489
             grind)
          | exact superpose b2e489 b2e22
          | exact resolve b2e22 b2e489
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e489
        have b2e546 : False := by grind
        exact b2e546
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ x)) with h1a | h1a
      · have b3e20 : (M.op (M.op x x) x) ≠ (M.op (M.op y y) x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e55 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X1) X0)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e63 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e25 X0 X1
             have i₂ := b6e59 X1 (τ X0)
             grind)
          | exact superpose b6e59 b6e25
          | (have j1 := b6e59 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b6e25 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e59 (σ X1) (σ X0)
             grind)
          | exact superpose b6e59 b6e18
          | (have j1 := b6e59 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b6e18 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e119 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e63 (σ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e63
          | exact resolve b6e63 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e135 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e119 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e119
          | (have j0 := b6e119 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b6e119 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e119
        have b6e469 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e64 x y
             grind)
          | exact superpose b6e64 b6e19
          | (have j1 := b6e64 x y
             grind)
          | exact resolve b6e19 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e469
             have i₂ := b6e135 x y
             grind)
          | exact superpose b6e135 b6e469
          | (have j1 := b6e135 (σ x) (σ y)
             grind)
          | (have r₁ := b6e469
             have r₂ := b6e135 x y
             grind)
          | (have r₁ := b6e469
             have r₂ := b6e135 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b6e469
             have r₂ := b6e135 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b6e469 b6e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e135 b6e469
        have b6e484 : (σ x) = (σ y) ∨ x = y := by grind
        clear b6e483
        have b6e486 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e484
             have r₂ := b6e21
             grind)
          | exact resolve b6e484 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e484
        have b6e539 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e486
             grind)
          | exact superpose b6e486 b6e13
          | exact resolve b6e13 b6e486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e486
        have b6e572 : x = y := by
          first
          | (have i₁ := b6e539
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e539
          | exact resolve b6e539 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e539
        have b6e575 : False := by grind
        exact b6e575
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ x)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) := by
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
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e66 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X1) X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e71 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e66 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e80 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e72 X1 (τ X0)
               grind)
            | exact superpose b8e72 b8e27
            | (have j1 := b8e72 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e27 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e72 (σ X1) (σ X0)
               grind)
            | exact superpose b8e72 b8e19
            | (have j1 := b8e72 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e139 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e80 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e80
            | exact resolve b8e80 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e155 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e139 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e139
            | (have j0 := b8e139 (σ (k X1 X0)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e139 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e474 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
          have b8e481 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e474
               have r₂ := b8e24
               grind)
            | exact resolve b8e474 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e474
          have b8e491 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e481
               have i₂ := b8e155 x y
               grind)
            | exact superpose b8e155 b8e481
            | (have j1 := b8e155 x y
               grind)
            | (have r₁ := b8e481
               have r₂ := b8e155 x y
               grind)
            | (have r₁ := b8e481
               have r₂ := b8e155 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e481
               have r₂ := b8e155 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e481 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155 b8e481
          have b8e492 : x = y := by grind
          clear b8e491
          have b8e494 : False := by grind
          exact b8e494

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),X) = m(m(Y,Y),Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxx_ppyyy_pyx_x_pyx_x_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) a ≠ M.op (M.op b b) b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b b) b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) a = M.op (M.op b b) b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b b) b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) a = M.op (M.op b b) b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op (M.op b b) b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) x) (M.op (M.op y y) y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x x) x) = (M.op (M.op y y) y) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e43 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op x x) x) ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 X0 x
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
      have b0e44 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ y) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 X0 (σ x)
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
      have b0e242 : (M.op x y) = (k y x) := by
        first
        | (have j0 := b0e43 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e264 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have j0 := b0e44 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e266 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e264
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e264
        | exact resolve b0e264 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e264
      have b0e271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e266
           have i₂ := b0e242
           grind)
        | exact superpose b0e242 b0e266
        | exact resolve b0e266 b0e242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e242 b0e266
      have b0e273 : False := by grind
      exact b0e273
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op (M.op x x) x) = (M.op (M.op y y) y) := by grind
        have b1e21 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e37 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op x x) x) ∨ (k y X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 y X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 X0 x
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
        have b1e65 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X1) = X1 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e17 X0 X2
             have i₂ := b1e17 X1 X2
             grind)
          | (have i₁ := b1e17 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e17
          | (have j0 := b1e17 X1 X2
             have j1 := b1e17 X1 X2
             grind)
          | exact resolve b1e17 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X1 X2
             have i₂ := b1e17 X0 X2
             grind)
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X0 X1
             have j1 := b1e17 X0 X2
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X1 X0
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 (M.op (M.op X1 X1) X1) X1
             have r₂ := b1e17 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e88 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b1e65 X1 X1 X2
             have j1 := b1e75 X1 X1 X2
             grind)
          | (have r₁ := b1e65 X0 X1 X2
             have r₂ := b1e75 X0 X1 X2
             grind)
          | (have r₁ := b1e65 X1 X0 X2
             have r₂ := b1e75 X0 X1 X2
             grind)
          | (have r₁ := b1e65 X0 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
             have r₂ := b1e75 (M.op (M.op X1 X1) X1) X1 X2
             grind)
          | exact resolve b1e65 b1e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e75
        have b1e126 : (M.op x y) = (k y x) := by
          first
          | (have j0 := b1e37 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e214 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e88 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88
        have b1e215 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e214 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e214
        have b1e216 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e215 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e215
        have b1e338 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e216 (σ X1) (σ X0)
             grind)
          | exact superpose b1e216 b1e18
          | (have j1 := b1e216 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e216
        have b1e2463 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e338 x y
             grind)
          | exact superpose b1e338 b1e19
          | (have j1 := b1e338 x y
             grind)
          | exact resolve b1e19 b1e338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e338
        have b1e2512 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e2463
             have i₂ := b1e126
             grind)
          | exact superpose b1e126 b1e2463
          | exact resolve b1e2463 b1e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2463
        have b1e2513 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b1e2512
        have b1e2662 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e2513
             grind)
          | exact superpose b1e2513 b1e19
          | exact resolve b1e19 b1e2513
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2663 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e2513
             grind)
          | exact superpose b1e2513 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e2513
             grind)
          | exact resolve b1e16 b1e2513
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2513
        have b1e2664 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b1e2663
        have b1e2665 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b1e2664
             have r₂ := b1e21
             grind)
          | exact resolve b1e2664 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2664
        have b1e2668 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e2665
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e2665
          | exact resolve b1e2665 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2665
        have b1e2669 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e2668
             have i₂ := b1e126
             grind)
          | exact superpose b1e126 b1e2668
          | exact resolve b1e2668 b1e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126 b1e2668
        have b1e2670 : False := by grind
        exact b1e2670
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op x x) x) = (M.op (M.op y y) y) := by grind
        have b2e21 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op x x) x) ∨ (k y X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 X0 x
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
        have b2e67 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X1) = X1 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X0 X2
             have i₂ := b2e17 X1 X2
             grind)
          | (have i₁ := b2e17 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e17
          | (have j0 := b2e17 X1 X2
             have j1 := b2e17 X1 X2
             grind)
          | exact resolve b2e17 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e77 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X2
             have i₂ := b2e17 X0 X2
             grind)
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X0 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X0
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 (M.op (M.op X1 X1) X1) X1
             have r₂ := b2e17 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e92 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e67 X1 X1 X2
             have j1 := b2e77 X1 X1 X2
             grind)
          | (have r₁ := b2e67 X0 X1 X2
             have r₂ := b2e77 X0 X1 X2
             grind)
          | (have r₁ := b2e67 X1 X0 X2
             have r₂ := b2e77 X0 X1 X2
             grind)
          | (have r₁ := b2e67 X0 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
             have r₂ := b2e77 (M.op (M.op X1 X1) X1) X1 X2
             grind)
          | exact resolve b2e67 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67 b2e77
        have b2e152 : (M.op x y) = (k y x) := by
          first
          | (have j0 := b2e37 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e221 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e92 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92
        have b2e222 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e221 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e221
        have b2e223 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e222 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e222
        have b2e265 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e223 (σ X1) (σ X0)
             grind)
          | exact superpose b2e223 b2e18
          | (have j1 := b2e223 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e223
        have b2e1897 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e265 x y
             grind)
          | exact superpose b2e265 b2e19
          | (have j1 := b2e265 x y
             grind)
          | exact resolve b2e19 b2e265
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e265
        have b2e1945 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1897
             have i₂ := b2e152
             grind)
          | exact superpose b2e152 b2e1897
          | exact resolve b2e1897 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1897
        have b2e1946 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e1945
        have b2e2182 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e1946
             grind)
          | exact superpose b2e1946 b2e19
          | exact resolve b2e19 b2e1946
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2183 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b2e16 (σ y) (σ x)
             have i₂ := b2e1946
             grind)
          | exact superpose b2e1946 b2e16
          | (have j0 := b2e16 (σ x) (σ y)
             grind)
          | (have r₁ := b2e16 (σ y) (σ x)
             have r₂ := b2e1946
             grind)
          | exact resolve b2e16 b2e1946
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1946
        have b2e2184 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b2e2183
        have b2e2185 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b2e2184
             have r₂ := b2e21
             grind)
          | exact resolve b2e2184 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2184
        have b2e2187 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b2e2185
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e2185
          | exact resolve b2e2185 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2185
        have b2e2188 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b2e2187
             have i₂ := b2e152
             grind)
          | exact superpose b2e152 b2e2187
          | exact resolve b2e2187 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e152 b2e2187
        have b2e2189 : False := by grind
        exact b2e2189
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op (M.op x x) x) ≠ (M.op (M.op y y) y) := by grind
        have b3e22 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e37 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 X0 (σ x)
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
        have b3e67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op x x) x) ∨ (k y X0) = (M.op X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e20
             have i₂ := b3e17 y X0
             grind)
          | (have i₁ := b3e20
             have i₂ := b3e17 X0 y
             grind)
          | exact superpose b3e17 b3e20
          | (have j1 := b3e17 y X0
             grind)
          | (have r₁ := b3e20
             have r₂ := b3e17 x y
             grind)
          | (have r₁ := b3e20
             have r₂ := b3e17 y x
             grind)
          | exact resolve b3e20 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e154 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have j0 := b3e37 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e156 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e154
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e154
          | exact resolve b3e154 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e154
        have b3e198 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
          first
          | (have j0 := b3e67 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e199 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e156
             grind)
          | exact superpose b3e156 b3e19
          | exact resolve b3e19 b3e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156
        have b3e341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e199
             have i₂ := b3e198
             grind)
          | exact superpose b3e198 b3e199
          | exact resolve b3e199 b3e198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e198
        have b3e342 : y = (M.op x y) := by grind
        clear b3e341
        have b3e354 : y ≠ y ∨ (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e342
             grind)
          | exact superpose b3e342 b3e16
          | (have j0 := b3e16 x y
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e342
             grind)
          | exact resolve b3e16 b3e342
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e355 : (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ y = (k y x) := by grind
        clear b3e354
        have b3e356 : y = (k y x) := by
          first
          | (have r₁ := b3e355
             have r₂ := b3e20
             grind)
          | exact resolve b3e355 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e355
        have b3e377 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e199
             have i₂ := b3e356
             grind)
          | exact superpose b3e356 b3e199
          | exact resolve b3e199 b3e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e199 b3e356
        have b3e398 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e377
             have i₂ := b3e342
             grind)
          | exact superpose b3e342 b3e377
          | exact resolve b3e377 b3e342
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e342 b3e377
        have b3e399 : False := by grind
        exact b3e399
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op (M.op x x) x) ≠ (M.op (M.op y y) y) := by grind
          have b4e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e71 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X1) = X1 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e18 X0 X2
               have i₂ := b4e18 X1 X2
               grind)
            | (have i₁ := b4e18 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e18
            | (have j0 := b4e18 X1 X2
               have j1 := b4e18 X1 X2
               grind)
            | exact resolve b4e18 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e81 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X1 X2
               have i₂ := b4e18 X0 X2
               grind)
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X1
               have j1 := b4e18 X0 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X0
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 (M.op (M.op X1 X1) X1) X1
               have r₂ := b4e18 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e94 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e71 X1 X1 X2
               have j1 := b4e81 X1 X1 X2
               grind)
            | (have r₁ := b4e71 X0 X1 X2
               have r₂ := b4e81 X0 X1 X2
               grind)
            | (have r₁ := b4e71 X1 X0 X2
               have r₂ := b4e81 X0 X1 X2
               grind)
            | (have r₁ := b4e71 X0 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
               have r₂ := b4e81 (M.op (M.op X1 X1) X1) X1 X2
               grind)
            | exact resolve b4e71 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71 b4e81
          have b4e221 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e94 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e222 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e221 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e221
          have b4e223 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e222 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e222
          have b4e281 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X0 X1
               have i₂ := b4e223 X1 (τ X0)
               grind)
            | exact superpose b4e223 b4e26
            | (have j1 := b4e223 X1 (τ X0)
               grind)
            | exact resolve b4e26 b4e223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e223 (σ X1) (σ X0)
               grind)
            | exact superpose b4e223 b4e19
            | (have j1 := b4e223 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223
          have b4e1517 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e281 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e281
            | exact resolve b4e281 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e281
          have b4e1580 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e1517 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e1517
            | (have j0 := b4e1517 X0 X1
               grind)
            | exact resolve b4e1517 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1517
          have b4e1930 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e282 x y
               grind)
            | exact superpose b4e282 b4e20
            | (have j1 := b4e282 x y
               grind)
            | exact resolve b4e20 b4e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1964 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e282 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e282
          have b4e2911 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e1930
               have i₂ := b4e1580 x y
               grind)
            | exact superpose b4e1580 b4e1930
            | (have j1 := b4e1580 (σ x) (σ y)
               grind)
            | (have r₁ := b4e1930
               have r₂ := b4e1580 x y
               grind)
            | exact resolve b4e1930 b4e1580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1930
          have b4e2912 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b4e2911
          have b4e3074 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e2912
               grind)
            | exact superpose b4e2912 b4e20
            | exact resolve b4e20 b4e2912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3075 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e2912
               grind)
            | exact superpose b4e2912 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e2912
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e2912
               grind)
            | exact resolve b4e17 b4e2912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2912
          have b4e3076 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b4e3075
          have b4e3077 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e3076
               have r₂ := b4e23
               grind)
            | exact resolve b4e3076 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3076
          have b4e3079 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e3077
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e3077
            | exact resolve b4e3077 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3077
          have b4e3397 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e1580 x y
               have i₂ := b4e3079
               grind)
            | exact superpose b4e3079 b4e1580
            | (have j0 := b4e1580 x y
               grind)
            | exact resolve b4e1580 b4e3079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1580 b4e3079
          have b4e3429 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b4e3397
          have b4e3458 : y = (M.op x y) := by
            first
            | (have r₁ := b4e3429
               have r₂ := b4e3074
               grind)
            | exact resolve b4e3429 b4e3074
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3074 b4e3429
          have b4e3606 : y ≠ y ∨ (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e3458
               grind)
            | exact superpose b4e3458 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e3458
               grind)
            | exact resolve b4e17 b4e3458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3607 : (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ y = (k y x) := by grind
          clear b4e3606
          have b4e3608 : y = (k y x) := by
            first
            | (have r₁ := b4e3607
               have r₂ := b4e21
               grind)
            | exact resolve b4e3607 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3607
          have b4e3781 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e1964 x y
               have i₂ := b4e3608
               grind)
            | exact superpose b4e3608 b4e1964
            | (have j0 := b4e1964 x y
               grind)
            | exact resolve b4e1964 b4e3608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1964 b4e3608
          have b4e3786 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b4e3781
          have b4e4138 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e3786
               grind)
            | exact superpose b4e3786 b4e20
            | exact resolve b4e20 b4e3786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3786
          have b4e4142 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e4138
               have i₂ := b4e3458
               grind)
            | exact superpose b4e3458 b4e4138
            | exact resolve b4e4138 b4e3458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3458 b4e4138
          have b4e4143 : False := by grind
          exact b4e4143
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op (M.op x x) x) ≠ (M.op (M.op y y) y) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e47 (σ X0)
               grind)
            | exact superpose b5e47 b5e19
            | exact resolve b5e19 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e49 X0
               have i₂ := b5e47 X0
               grind)
            | exact superpose b5e47 b5e49
            | exact resolve b5e49 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e49
          have b5e62 : x ≠ x ∨ (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ x = (k x y) := by
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
          have b5e63 : (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ x = (k x y) := by grind
          clear b5e62
          have b5e64 : x = (k x y) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (M.op (σ X1) (σ X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e84 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (M.op X1 X1)) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e82 X0 X1
               have i₂ := b5e56 X1
               grind)
            | exact superpose b5e56 b5e82
            | (have j0 := b5e82 X0 X1
               grind)
            | exact resolve b5e82 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e93 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X1)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e84 X0 X1
               have i₂ := b5e56 X0
               grind)
            | exact superpose b5e56 b5e84
            | (have j0 := b5e84 X0 X1
               grind)
            | exact resolve b5e84 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e121 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e56 y
               grind)
            | exact superpose b5e56 b5e23
            | exact resolve b5e23 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e129 : (M.op (σ (M.op x x)) (σ x)) ≠ (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b5e121
               have i₂ := b5e56 x
               grind)
            | exact superpose b5e56 b5e121
            | exact resolve b5e121 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e121
          have b5e623 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ (M.op X1 X1)) (σ X1)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e93 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e1179 : (σ x) ≠ (σ x) ∨ (M.op (σ (M.op x x)) (σ x)) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e623 y x
               have i₂ := b5e64
               grind)
            | exact superpose b5e64 b5e623
            | (have j0 := b5e623 y x
               grind)
            | exact resolve b5e623 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e623
          have b5e1183 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e1179
          have b5e1187 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e1183
               have r₂ := b5e129
               grind)
            | exact resolve b5e1183 b5e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129 b5e1183
          have b5e1198 : False := by grind
          exact b5e1198
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op (M.op x x) x) ≠ (M.op (M.op y y) y) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e37 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 X0 (σ x)
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
        have b6e76 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op x x) x) ∨ (k y X0) = (M.op X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e17 y X0
             grind)
          | (have i₁ := b6e20
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e20
          | (have j1 := b6e17 y X0
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 x y
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 y x
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e165 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have j0 := b6e37 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e167 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e165
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e165
          | exact resolve b6e165 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e165
        have b6e172 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e167
             grind)
          | exact superpose b6e167 b6e19
          | exact resolve b6e19 b6e167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e167
        have b6e194 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
          first
          | (have j0 := b6e76 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e317 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e172
             have i₂ := b6e194
             grind)
          | exact superpose b6e194 b6e172
          | exact resolve b6e172 b6e194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e194
        have b6e318 : y = (M.op x y) := by grind
        clear b6e317
        have b6e330 : y ≠ y ∨ (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e318
             grind)
          | exact superpose b6e318 b6e16
          | (have j0 := b6e16 x y
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e318
             grind)
          | exact resolve b6e16 b6e318
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e331 : (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ y = (k y x) := by grind
        clear b6e330
        have b6e332 : y = (k y x) := by
          first
          | (have r₁ := b6e331
             have r₂ := b6e20
             grind)
          | exact resolve b6e331 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e331
        have b6e353 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e172
             have i₂ := b6e332
             grind)
          | exact superpose b6e332 b6e172
          | exact resolve b6e172 b6e332
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e172 b6e332
        have b6e374 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b6e353
             have i₂ := b6e318
             grind)
          | exact superpose b6e318 b6e353
          | exact resolve b6e353 b6e318
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e318 b6e353
        have b6e375 : False := by grind
        exact b6e375
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op (M.op x x) x) ≠ (M.op (M.op y y) y) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e62 : (σ x) ≠ (σ x) ∨ (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e63 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e62
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
          have b7e84 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op x x) x) ∨ (k X0 y) = (M.op y X0) ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e18 X0 y
               grind)
            | (have i₁ := b7e21
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e21
            | (have j1 := b7e18 X0 y
               grind)
            | (have r₁ := b7e21
               have r₂ := b7e18 x y
               grind)
            | (have r₁ := b7e21
               have r₂ := b7e18 y x
               grind)
            | exact resolve b7e21 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e133 : (M.op y x) = (k x y) ∨ x = (M.op y x) := by
            first
            | (have j0 := b7e84 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e134 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b7e133
               have r₂ := b7e22
               grind)
            | exact resolve b7e133 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133
          have b7e135 : x = (M.op y x) := by
            first
            | (have i₁ := b7e134
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e134
            | exact resolve b7e134 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e134
          have b7e136 : False := by grind
          exact b7e136
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op (M.op x x) x) ≠ (M.op (M.op y y) y) := by grind
          have b8e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
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
          have b8e80 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X1) = X1 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e18 X0 X2
               have i₂ := b8e18 X1 X2
               grind)
            | (have i₁ := b8e18 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e18
            | (have j0 := b8e18 X1 X2
               have j1 := b8e18 X1 X2
               grind)
            | exact resolve b8e18 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e90 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X1 X2
               have i₂ := b8e18 X0 X2
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X2
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X0
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 (M.op (M.op X1 X1) X1) X1
               have r₂ := b8e18 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e105 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e80 X1 X1 X2
               have j1 := b8e90 X1 X1 X2
               grind)
            | (have r₁ := b8e80 X0 X1 X2
               have r₂ := b8e90 X0 X1 X2
               grind)
            | (have r₁ := b8e80 X1 X0 X2
               have r₂ := b8e90 X0 X1 X2
               grind)
            | (have r₁ := b8e80 X0 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))
               have r₂ := b8e90 (M.op (M.op X1 X1) X1) X1 X2
               grind)
            | exact resolve b8e80 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80 b8e90
          have b8e207 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e105 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e208 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e207 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207
          have b8e209 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e208 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208
          have b8e254 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e209 X1 (τ X0)
               grind)
            | exact superpose b8e209 b8e26
            | (have j1 := b8e209 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e255 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e209 (σ X1) (σ X0)
               grind)
            | exact superpose b8e209 b8e19
            | (have j1 := b8e209 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209
          have b8e1559 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e254 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e254
            | exact resolve b8e254 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e254
          have b8e1622 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1559 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e1559
            | (have j0 := b8e1559 X0 X1
               grind)
            | exact resolve b8e1559 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1559
          have b8e1916 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e255 x y
               grind)
            | exact superpose b8e255 b8e20
            | (have j1 := b8e255 x y
               grind)
            | exact resolve b8e20 b8e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1952 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e255 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e255
          have b8e3024 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1916
               have i₂ := b8e1622 x y
               grind)
            | exact superpose b8e1622 b8e1916
            | (have j1 := b8e1622 (σ x) (σ y)
               grind)
            | (have r₁ := b8e1916
               have r₂ := b8e1622 x y
               grind)
            | exact resolve b8e1916 b8e1622
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1916
          have b8e3025 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b8e3024
          have b8e3191 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3025
               grind)
            | exact superpose b8e3025 b8e20
            | exact resolve b8e20 b8e3025
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3192 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e3025
               grind)
            | exact superpose b8e3025 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e3025
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e3025
               grind)
            | exact resolve b8e17 b8e3025
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3025
          have b8e3193 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e3192
          have b8e3194 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e3193
               have r₂ := b8e23
               grind)
            | exact resolve b8e3193 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3193
          have b8e3196 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e3194
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e3194
            | exact resolve b8e3194 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3194
          have b8e3501 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1622 x y
               have i₂ := b8e3196
               grind)
            | exact superpose b8e3196 b8e1622
            | (have j0 := b8e1622 x y
               grind)
            | exact resolve b8e1622 b8e3196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1622 b8e3196
          have b8e3533 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b8e3501
          have b8e3562 : y = (M.op x y) := by
            first
            | (have r₁ := b8e3533
               have r₂ := b8e3191
               grind)
            | exact resolve b8e3533 b8e3191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3191 b8e3533
          have b8e3719 : y ≠ y ∨ (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e3562
               grind)
            | exact superpose b8e3562 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e3562
               grind)
            | exact resolve b8e17 b8e3562
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3720 : (M.op (M.op x x) x) = (M.op (M.op y y) y) ∨ y = (k y x) := by grind
          clear b8e3719
          have b8e3721 : y = (k y x) := by
            first
            | (have r₁ := b8e3720
               have r₂ := b8e21
               grind)
            | exact resolve b8e3720 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3720
          have b8e3898 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1952 x y
               have i₂ := b8e3721
               grind)
            | exact superpose b8e3721 b8e1952
            | (have j0 := b8e1952 x y
               grind)
            | exact resolve b8e1952 b8e3721
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1952 b8e3721
          have b8e3903 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e3898
          have b8e4275 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3903
               grind)
            | exact superpose b8e3903 b8e20
            | exact resolve b8e20 b8e3903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3903
          have b8e4279 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e4275
               have i₂ := b8e3562
               grind)
            | exact superpose b8e3562 b8e4275
            | exact resolve b8e4275 b8e3562
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3562 b8e4275
          have b8e4280 : False := by grind
          exact b8e4280

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),X) = m(Y,X) then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxx_pyx_pxx_y_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) a = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) a = M.op b a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e14 X0 (M.op X0 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e14 X0 (M.op X0 X0)
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 (M.op X0 X0)
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 (M.op X0 X0)
           have r₂ := b0e16 X0 (M.op X0 X0)
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 (M.op (M.op X0 X0) X0)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e89 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 X0
           have i₂ := b0e56 X0 X1
           grind)
        | (have i₁ := b0e32 X0
           have i₂ := b0e56 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e56 b0e32
        | (have j1 := b0e56 X1 X0
           grind)
        | exact resolve b0e32 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e56
      have b0e95 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e89 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89
      have b0e106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e95 (σ X1) (σ X0)
           grind)
        | exact superpose b0e95 b0e17
        | exact resolve b0e17 b0e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e106 X0 X1
           have i₂ := b0e95 X1 X0
           grind)
        | exact superpose b0e95 b0e106
        | exact resolve b0e106 b0e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95 b0e106
      have b0e826 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e115 x y
           grind)
        | exact superpose b0e115 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e115 x y
           grind)
        | exact resolve b0e18 b0e115
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115
      have b0e841 : False := by grind
      exact b0e841
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e40 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e15 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e15 X0 (M.op X0 X0)
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 (M.op X0 X0)
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 X0)
             have r₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 (M.op (M.op X0 X0) X0)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e40 X0
             have i₂ := b2e63 X0 X1
             grind)
          | (have i₁ := b2e40 X0
             have i₂ := b2e63 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e63 b2e40
          | (have j1 := b2e63 X1 X0
             grind)
          | exact resolve b2e40 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e63
        have b2e108 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e101 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e101
        have b2e121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e108 (σ X1) (σ X0)
             grind)
          | exact superpose b2e108 b2e18
          | exact resolve b2e18 b2e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e132 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e121 X0 X1
             have i₂ := b2e108 X1 X0
             grind)
          | exact superpose b2e108 b2e121
          | exact resolve b2e121 b2e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108 b2e121
        have b2e643 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e132 x y
             grind)
          | exact superpose b2e132 b2e19
          | (have r₁ := b2e19
             have r₂ := b2e132 x y
             grind)
          | exact resolve b2e19 b2e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e132
        have b2e655 : False := by grind
        exact b2e655
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e20 : (M.op (M.op x x) x) ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (M.op y x) ≠ (M.op y x) := by
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : False := by grind
          exact b4e27
        · have b5e21 : (M.op (M.op x x) x) ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op y x) ≠ (M.op y x) := by
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
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op (M.op x x) x) ≠ (M.op y x) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (σ y) (σ x)) := by grind
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
        have b6e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e24 X0 X1
             grind)
          | exact superpose b6e24 b6e13
          | exact resolve b6e13 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e25 X1 X0
             grind)
          | exact superpose b6e25 b6e13
          | exact resolve b6e13 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e40 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b6e15 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 (M.op X0 X0)
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 (M.op X0 X0)
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 (M.op X0 X0)
             have r₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 (M.op (M.op X0 X0) X0)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 X0
             have i₂ := b6e63 X0 X1
             grind)
          | (have i₁ := b6e40 X0
             have i₂ := b6e63 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e63 b6e40
          | (have j1 := b6e63 X1 X0
             grind)
          | exact resolve b6e40 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e63
        have b6e107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e101 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e101
        have b6e122 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e35 X0 X1
             have i₂ := b6e107 X1 (σ X0)
             grind)
          | exact superpose b6e107 b6e35
          | exact resolve b6e35 b6e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e125 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X0 X1
             have i₂ := b6e107 (σ X1) X0
             grind)
          | exact superpose b6e107 b6e29
          | exact resolve b6e29 b6e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e128 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e125 X0 X1
             have i₂ := b6e107 X1 (τ X0)
             grind)
          | exact superpose b6e107 b6e125
          | exact resolve b6e125 b6e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e131 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e122 X0 X1
             have i₂ := b6e107 (τ X1) X0
             grind)
          | exact superpose b6e107 b6e122
          | exact resolve b6e122 b6e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e107 b6e122
        have b6e272 : (M.op (τ (M.op (σ x) (σ x))) x) = (τ (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b6e128 (M.op (σ x) (σ x)) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e128
          | exact resolve b6e128 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128
        have b6e292 : (M.op (τ (M.op (σ x) (σ x))) x) = (M.op y (τ (σ x))) := by
          first
          | (have i₁ := b6e272
             have i₂ := b6e131 y (σ x)
             grind)
          | exact superpose b6e131 b6e272
          | exact resolve b6e272 b6e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e272
        have b6e302 : (M.op y x) = (M.op (τ (M.op (σ x) (σ x))) x) := by
          first
          | (have i₁ := b6e292
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e292
          | exact resolve b6e292 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e292
        have b6e307 : (M.op y x) = (M.op (M.op x (τ (σ x))) x) := by
          first
          | (have i₁ := b6e302
             have i₂ := b6e131 x (σ x)
             grind)
          | exact superpose b6e131 b6e302
          | exact resolve b6e302 b6e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e131 b6e302
        have b6e310 : (M.op (M.op x x) x) = (M.op y x) := by
          first
          | (have i₁ := b6e307
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e307
          | exact resolve b6e307 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e307
        have b6e313 : False := by grind
        exact b6e313
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) := by
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
        · have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e32 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b8e16 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e47 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 (M.op X0 X0)
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 (M.op X0 X0)
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 (M.op X0 X0)
               have r₂ := b8e18 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 (M.op (M.op X0 X0) X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e51 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47
          have b8e52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e85 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0
               have i₂ := b8e52 X0 X1
               grind)
            | (have i₁ := b8e32 X0
               have i₂ := b8e52 X0 (M.op X0 X0)
               grind)
            | exact superpose b8e52 b8e32
            | (have j1 := b8e52 X1 X0
               grind)
            | exact resolve b8e32 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e52
          have b8e92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e85 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e92 (σ X1) (σ X0)
               grind)
            | exact superpose b8e92 b8e19
            | exact resolve b8e19 b8e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e111 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e102 X0 X1
               have i₂ := b8e92 X1 X0
               grind)
            | exact superpose b8e92 b8e102
            | exact resolve b8e102 b8e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92 b8e102
          have b8e1000 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e111 x y
               grind)
            | exact superpose b8e111 b8e20
            | (have r₁ := b8e20
               have r₂ := b8e111 x y
               grind)
            | exact resolve b8e20 b8e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111
          have b8e1012 : False := by grind
          exact b8e1012
