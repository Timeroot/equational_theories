import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,m(X,X)) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxpxx_pyx_pxy_x_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a (M.op a a) ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a a)) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a (M.op a a) = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a a)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a (M.op a a) = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a a)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x (M.op x x)) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x (M.op x x)) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e97 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b0e27 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e100 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b0e28 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e102 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e100
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e100
        | exact resolve b0e100 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100
      have b0e103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e102
           have i₂ := b0e97
           grind)
        | exact superpose b0e97 b0e102
        | exact resolve b0e102 b0e97
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97 b0e102
      have b0e104 : False := by grind
      exact b0e104
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e21 : (M.op (σ x) (M.op (σ x) (σ x))) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b1e47 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e49 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e47
        have b1e50 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e49
             have r₂ := b1e21
             grind)
          | exact resolve b1e49 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : (σ x) = (σ (k x y)) := by
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
        have b1e55 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k x y)
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e13
          | exact resolve b1e13 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e56 : x = (k x y) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e55
          | exact resolve b1e55 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e68 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
          | (have r₁ := b1e15 X1 (M.op X1 (M.op X1 X1))
             have r₂ := b1e17 (M.op X1 (M.op X1 X1)) X1
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e68 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e81 : x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e74 x y
             grind)
          | exact superpose b1e74 b1e56
          | (have j1 := b1e74 x y
             grind)
          | exact resolve b1e56 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e74
        have b1e83 : x = (M.op x y) := by grind
        clear b1e81
        have b1e86 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e83
             grind)
          | exact superpose b1e83 b1e23
          | exact resolve b1e23 b1e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e83
        have b1e89 : False := by grind
        exact b1e89
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x (M.op x x)) = (M.op y x) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
          | (have r₁ := b2e15 X1 (M.op X1 (M.op X1 X1))
             have r₂ := b2e17 (M.op X1 (M.op X1 X1)) X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e73 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e67 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e74 (σ X0) (σ X1)
             grind)
          | exact superpose b2e74 b2e18
          | (have j1 := b2e74 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e96 : (M.op x y) = (k x y) := by
          first
          | (have j0 := b2e37 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e426 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e89 x y
             grind)
          | exact superpose b2e89 b2e19
          | (have j1 := b2e89 x y
             grind)
          | exact resolve b2e19 b2e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e439 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e426
             have r₂ := b2e22
             grind)
          | exact resolve b2e426 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e426
        have b2e443 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e439
             have i₂ := b2e96
             grind)
          | exact superpose b2e96 b2e439
          | exact resolve b2e439 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96 b2e439
        have b2e444 : False := by grind
        exact b2e444
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x (M.op x x)) ≠ (M.op y x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) := by grind
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
        have b3e38 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : x ≠ x ∨ (M.op x (M.op x x)) = (M.op y x) ∨ x = (k x y) := by
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
        have b3e49 : (M.op x (M.op x x)) = (M.op y x) ∨ x = (k x y) := by grind
        clear b3e47
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
        have b3e104 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b3e38 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e106 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e104
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e104
          | exact resolve b3e104 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104
        have b3e107 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e106
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e106
          | exact resolve b3e106 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e106
        have b3e108 : False := by grind
        exact b3e108
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x (M.op x x)) ≠ (M.op y x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (M.op (σ x) (M.op (σ x) (σ x))) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e48 : x ≠ x ∨ (M.op x (M.op x x)) = (M.op y x) ∨ x = (k x y) := by
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
          have b5e49 : (M.op x (M.op x x)) = (M.op y x) ∨ x = (k x y) := by grind
          clear b5e48
          have b5e50 : x = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e61 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e128 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e61 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e617 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e128 x y
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e128
            | (have j0 := b5e128 x y
               grind)
            | exact resolve b5e128 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e128
          have b5e621 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e617
          have b5e624 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e621
               have r₂ := b5e23
               grind)
            | exact resolve b5e621 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e621
          have b5e628 : False := by grind
          exact b5e628
    · rcases eq_or_ne (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e37 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e67 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
          | (have r₁ := b6e15 X1 (M.op X1 (M.op X1 X1))
             have r₂ := b6e17 (M.op X1 (M.op X1 X1)) X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e67 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e114 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b6e37 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e116 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e114
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e114
          | exact resolve b6e114 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114
        have b6e117 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e116
             grind)
          | exact superpose b6e116 b6e19
          | exact resolve b6e19 b6e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e116
        have b6e155 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e117
             have i₂ := b6e74 x y
             grind)
          | exact superpose b6e74 b6e117
          | (have j1 := b6e74 x y
             grind)
          | exact resolve b6e117 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74 b6e117
        have b6e156 : x = (M.op x y) := by grind
        clear b6e155
        have b6e157 : False := by grind
        exact b6e157
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ x) (M.op (σ x) (σ x))) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e40 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e41 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e42 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e23
               grind)
            | exact resolve b7e41 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e43 : (σ x) = (σ (k x y)) := by
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
          have b7e46 : (k x y) = (τ (σ x)) := by
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
          have b7e47 : x = (k x y) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e46
            | exact resolve b7e46 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
            | (have r₁ := b7e16 X1 (M.op X1 (M.op X1 X1))
               have r₂ := b7e18 (M.op X1 (M.op X1 X1)) X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
          have b7e68 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e62 x y
               grind)
            | exact superpose b7e62 b7e47
            | (have j1 := b7e62 x y
               grind)
            | exact resolve b7e47 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47 b7e62
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
          have b8e16 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
          have b8e54 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
            | (have r₁ := b8e16 X1 (M.op X1 (M.op X1 X1))
               have r₂ := b8e18 (M.op X1 (M.op X1 X1)) X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e59 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e60 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e60 (σ X0) (σ X1)
               grind)
            | exact superpose b8e60 b8e19
            | (have j1 := b8e60 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e78 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e60 X0 (τ X1)
               grind)
            | exact superpose b8e60 b8e26
            | (have j1 := b8e60 X0 (τ X1)
               grind)
            | exact resolve b8e26 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e60
          have b8e256 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e78 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e78
            | exact resolve b8e78 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e286 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e256 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e256
            | (have j0 := b8e256 X0 X1
               grind)
            | exact resolve b8e256 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256
          have b8e422 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e75 x y
               grind)
            | exact superpose b8e75 b8e20
            | (have j1 := b8e75 x y
               grind)
            | exact resolve b8e20 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e435 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e422
               have r₂ := b8e24
               grind)
            | exact resolve b8e422 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e422
          have b8e440 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e435
               have i₂ := b8e286 y x
               grind)
            | exact superpose b8e286 b8e435
            | (have j1 := b8e286 y x
               grind)
            | (have r₁ := b8e435
               have r₂ := b8e286 y x
               grind)
            | exact resolve b8e435 b8e286
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e286 b8e435
          have b8e441 : x = (M.op x y) := by grind
          clear b8e440
          have b8e443 : False := by grind
          exact b8e443

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,m(X,Y)) = m(X,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxpxy_pxy_x_y_pxy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a (M.op a b) ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a b)) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a (M.op a b) = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a b)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a (M.op a b) = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a b)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x (M.op x y)) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x (M.op x y)) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
      have b0e31 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e37 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
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
      have b0e38 : False := by grind
      exact b0e38
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b1e58 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b1e60 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e58 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e60 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e61 (σ X0)
             grind)
          | exact superpose b1e61 b1e18
          | exact resolve b1e18 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e65 X0
             have i₂ := b1e61 X0
             grind)
          | exact superpose b1e61 b1e65
          | exact resolve b1e65 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e65
        have b1e126 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e68 x
             grind)
          | exact superpose b1e68 b1e25
          | exact resolve b1e25 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e68
        have b1e131 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e126
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e126
          | exact resolve b1e126 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e126
        have b1e132 : False := by grind
        exact b1e132
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x (M.op x y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e39 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b2e60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
             have r₂ := b2e17 (M.op X0 X1) (M.op X0 (M.op X0 X1))
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X0 (M.op X0 X1)) (M.op X0 X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e63 (σ X0) (σ X1)
             grind)
          | exact superpose b2e63 b2e18
          | (have j1 := b2e63 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e466 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e68 x y
             grind)
          | exact superpose b2e68 b2e19
          | (have j1 := b2e68 x y
             grind)
          | exact resolve b2e19 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e476 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e466
             have r₂ := b2e22
             grind)
          | exact resolve b2e466 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e466
        have b2e482 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e476
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e476
          | exact resolve b2e476 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e476
        have b2e483 : False := by grind
        exact b2e483
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
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
        have b3e49 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b3e51 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e49 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e51 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e72 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e36
        have b3e75 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e72
             have i₂ := b3e52 y
             grind)
          | exact superpose b3e52 b3e72
          | exact resolve b3e72 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e72
        have b3e76 : False := by grind
        exact b3e76
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b4e106 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
          clear b4e58
          have b4e109 : False := by grind
          exact b4e109
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e39 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e46 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b6e67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
             have r₂ := b6e17 (M.op X0 X1) (M.op X0 (M.op X0 X1))
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X0 (M.op X0 X1)) (M.op X0 X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e67 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e69 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e76 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b6e46
             have i₂ := b6e70 x y
             grind)
          | exact superpose b6e70 b6e46
          | (have j1 := b6e70 x y
             grind)
          | (have r₁ := b6e46
             have r₂ := b6e70 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e46
             have r₂ := b6e70 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e46 b6e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46 b6e70
        have b6e77 : x = y := by grind
        clear b6e76
        have b6e78 : False := by grind
        exact b6e78
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
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
               have r₂ := b8e18 (M.op X0 X1) (M.op X0 (M.op X0 X1))
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 (M.op X0 X1)) (M.op X0 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e61 (σ X0) (σ X1)
               grind)
            | exact superpose b8e61 b8e19
            | (have j1 := b8e61 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e61 (τ X0) X1
               grind)
            | exact superpose b8e61 b8e26
            | (have j1 := b8e61 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e61
          have b8e119 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e66 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e66
            | exact resolve b8e66 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e119 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e119
            | (have j0 := b8e119 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e119 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e461 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e65 x y
               grind)
            | exact superpose b8e65 b8e20
            | (have j1 := b8e65 x y
               grind)
            | exact resolve b8e20 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e471 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e461
               have r₂ := b8e24
               grind)
            | exact resolve b8e461 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e461
          have b8e480 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e471
               have i₂ := b8e137 x y
               grind)
            | exact superpose b8e137 b8e471
            | (have j1 := b8e137 x y
               grind)
            | (have r₁ := b8e471
               have r₂ := b8e137 x y
               grind)
            | (have r₁ := b8e471
               have r₂ := b8e137 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e471
               have r₂ := b8e137 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e471 b8e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137 b8e471
          have b8e481 : x = y := by grind
          clear b8e480
          have b8e483 : False := by grind
          exact b8e483

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,m(Y,X)) = m(X,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxpyx_pxy_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a (M.op b a) ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b a)) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a (M.op b a) = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b a)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a (M.op b a) = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b a)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x (M.op y x)) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x (M.op y x)) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by grind
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x (M.op y x)) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ y) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by
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
        have b1e41 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b1e44 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e46 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e44
        have b1e47 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e23
             grind)
          | exact resolve b1e46 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e46
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
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e48
          | exact resolve b1e48 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e48
        have b1e50 : False := by grind
        exact b1e50
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x (M.op y x)) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e54 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b2e59 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b2e60 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e59
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e59
          | exact resolve b2e59 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e59
        have b2e61 : False := by grind
        exact b2e61
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x (M.op y x)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : y ≠ (M.op x (M.op y x)) := by
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
        have b3e44 : (σ y) ≠ (σ (k x y)) := by
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
        have b3e47 : y ≠ y ∨ y = (M.op x (M.op y x)) ∨ y = (k x y) := by
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
        have b3e50 : y = (M.op x (M.op y x)) ∨ y = (k x y) := by grind
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
        have b3e66 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e44
          | exact resolve b3e44 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e52
        have b3e67 : False := by grind
        exact b3e67
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x (M.op y x)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ (M.op x (M.op y x)) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : y ≠ y ∨ y = (M.op x (M.op y x)) ∨ y = (k x y) := by
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
          have b5e51 : y = (M.op x (M.op y x)) ∨ y = (k x y) := by grind
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
          have b5e58 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          have b5e60 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b5e58
          have b5e63 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e60
               have r₂ := b5e24
               grind)
            | exact resolve b5e60 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e64 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e63
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e63
            | exact resolve b5e63 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e65 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e64
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e64
            | exact resolve b5e64 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e64
          have b5e66 : False := by grind
          exact b5e66
    · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x (M.op y x)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by grind
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
        have b6e55 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b6e56 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
        clear b6e55
        have b6e59 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e56
             have r₂ := b6e21
             grind)
          | exact resolve b6e56 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e60 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e59
             grind)
          | exact superpose b6e59 b6e41
          | exact resolve b6e41 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e59
        have b6e61 : False := by grind
        exact b6e61
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x (M.op y x)) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e45 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e25
               grind)
            | exact resolve b7e44 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e44
          have b7e46 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e45
            | exact resolve b7e45 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e14
            | exact resolve b7e14 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : y = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e59 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e21
            | (have j1 := b7e18 x y
               grind)
            | (have r₁ := b7e21
               have r₂ := b7e18 x y
               grind)
            | exact resolve b7e21 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e60 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b7e59
          have b7e63 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e64 : y = (M.op x y) := by
            first
            | (have i₁ := b7e63
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e63
            | exact resolve b7e63 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50 b7e63
          have b7e65 : False := by grind
          exact b7e65
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x (M.op y x)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e51 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          have b8e52 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
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

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,m(Y,X)) = m(X,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxpyx_pxy_x_y_pxy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a (M.op b a) ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b a)) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a (M.op b a) = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b a)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a (M.op b a) = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b a)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x (M.op y x)) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x (M.op y x)) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
      have b0e31 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x (M.op y x)) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by grind
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
        have b1e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x x) := by
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
        have b1e51 : (M.op x x) = (k x x) := by grind
        clear b1e50
        have b1e58 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e24
        have b1e59 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e58
        have b1e62 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e59
          | exact resolve b1e59 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e63 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
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
        have b1e83 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
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
        have b1e88 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x (M.op y x)) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e39 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b2e60 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          | (have r₁ := b2e21
             have r₂ := b2e17 (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (σ x)))
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y))
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b2e60
        have b2e64 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e61
             have r₂ := b2e22
             grind)
          | exact resolve b2e61 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e65 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e64
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e64
          | exact resolve b2e64 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e66 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e65
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e65
          | exact resolve b2e65 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e65
        have b2e67 : False := by grind
        exact b2e67
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by grind
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
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
    · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x (M.op y x)) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e39 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e42 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b6e65 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by
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
          | (have r₁ := b6e20
             have r₂ := b6e17 (M.op x y) (M.op x (M.op y x))
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 (M.op x (M.op y x)) (M.op x y)
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e66 : x = y ∨ (M.op x y) = (k x y) := by grind
        clear b6e65
        have b6e69 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e66
             have r₂ := b6e21
             grind)
          | exact resolve b6e66 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e74 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e69
             grind)
          | exact superpose b6e69 b6e42
          | exact resolve b6e42 b6e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e69
        have b6e77 : False := by grind
        exact b6e77
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
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x (M.op y x)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e58 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
            | (have r₁ := b8e23
               have r₂ := b8e18 (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (σ x)))
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y))
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e59 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by
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
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op x y) (M.op x (M.op y x))
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op x (M.op y x)) (M.op x y)
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : x = y ∨ (M.op x y) = (k x y) := by grind
          clear b8e59
          have b8e61 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b8e58
          have b8e64 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e60
               have r₂ := b8e22
               grind)
            | exact resolve b8e60 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e65 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e61
               have r₂ := b8e24
               grind)
            | exact resolve b8e61 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e66 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e65
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e65
            | exact resolve b8e65 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e67 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e66
               have i₂ := b8e64
               grind)
            | exact superpose b8e64 b8e66
            | exact resolve b8e66 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e66
          have b8e68 : False := by grind
          exact b8e68

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,m(Y,Y)) = m(Y,m(X,Y)) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxpyy_pypxy_x_y_pyx_x_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ ((Lf 1) ⋆ (Lf 1))) ((Lf 1) ⋆ ((Lf 0) ⋆ (Lf 1))) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ ((Lf 1) ⋆ (Lf 1))) ((Lf 1) ⋆ ((Lf 0) ⋆ (Lf 1))) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a (M.op b b) ≠ M.op b (M.op a b) ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b b)) (M.op b (M.op a b))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a (M.op b b) = M.op b (M.op a b) ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b b)) (M.op b (M.op a b))).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a (M.op b b) = M.op b (M.op a b) ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a (M.op b b)) (M.op b (M.op a b))).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x (M.op y y)) (M.op y (M.op x y)) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e75 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e16 X1 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e16 X1 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X0 X1))
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e75 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e78 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e77 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e87 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
      have b0e88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
      have b0e145 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e87 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e87
        | exact resolve b0e87 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e163 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e145 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e145
        | (have j0 := b0e145 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e145 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145
      have b0e503 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e88 x y
           grind)
        | exact superpose b0e88 b0e18
        | (have j1 := b0e88 x y
           grind)
        | exact resolve b0e18 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e526 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e503
           have i₂ := b0e163 x y
           grind)
        | exact superpose b0e163 b0e503
        | (have j1 := b0e163 (σ x) (σ y)
           grind)
        | (have r₁ := b0e503
           have r₂ := b0e163 x y
           grind)
        | (have r₁ := b0e503
           have r₂ := b0e163 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e503
           have r₂ := b0e163 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e503 b0e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e163 b0e503
      have b0e527 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e526
      have b0e534 : x = (τ (σ y)) ∨ x = y := by
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
      have b0e565 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e534
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e534
        | exact resolve b0e534 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e534
      have b0e566 : x = y := by grind
      clear b0e565
      have b0e620 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e566
           grind)
        | exact superpose b0e566 b0e18
        | exact resolve b0e18 b0e566
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e566
      have b0e628 : False := by grind
      exact b0e628
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ y) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (M.op (σ y) (σ y))) := by
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
        have b2e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e17 X1 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X0 X1))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
        have b2e149 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
        have b2e167 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e149 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e149
          | (have j0 := b2e149 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b2e149 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e149
        have b2e477 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
        have b2e489 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e477
             have r₂ := b2e22
             grind)
          | exact resolve b2e477 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e477
        have b2e497 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b2e489
             have i₂ := b2e167 x y
             grind)
          | exact superpose b2e167 b2e489
          | (have j1 := b2e167 x y
             grind)
          | (have r₁ := b2e489
             have r₂ := b2e167 x y
             grind)
          | (have r₁ := b2e489
             have r₂ := b2e167 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b2e489
             have r₂ := b2e167 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b2e489 b2e167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e167 b2e489
        have b2e498 : x = y := by grind
        clear b2e497
        have b2e502 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e498
             grind)
          | exact superpose b2e498 b2e22
          | exact resolve b2e22 b2e498
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e498
        have b2e506 : False := by grind
        exact b2e506
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))) with h1a | h1a
      · have b3e20 : (M.op x (M.op y y)) ≠ (M.op y (M.op x y)) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e61 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X1 X1
             have i₂ := b6e17 X1 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X1
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X0 X1))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b6e74 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
        have b6e157 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e74 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e74
          | exact resolve b6e74 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e157 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e157
          | (have j0 := b6e157 (σ (k X0 X1)) (σ (M.op X1 X0))
             grind)
          | exact resolve b6e157 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e157
        have b6e495 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e73 x y
             grind)
          | exact superpose b6e73 b6e19
          | (have j1 := b6e73 x y
             grind)
          | exact resolve b6e19 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e495
             have i₂ := b6e173 y x
             grind)
          | exact superpose b6e173 b6e495
          | (have j1 := b6e173 (σ x) (σ y)
             grind)
          | (have r₁ := b6e495
             have r₂ := b6e173 y x
             grind)
          | (have r₁ := b6e495
             have r₂ := b6e173 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b6e495
             have r₂ := b6e173 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b6e495 b6e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e173 b6e495
        have b6e524 : (σ x) = (σ y) ∨ x = y := by grind
        clear b6e523
        have b6e526 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e524
             have r₂ := b6e21
             grind)
          | exact resolve b6e524 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e524
        have b6e581 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e526
             grind)
          | exact superpose b6e526 b6e13
          | exact resolve b6e13 b6e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e526
        have b6e614 : x = y := by
          first
          | (have i₁ := b6e581
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e581
          | exact resolve b6e581 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e581
        have b6e618 : False := by grind
        exact b6e618
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ y) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (M.op (σ y) (σ y))) := by
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
          have b8e16 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e71 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X1 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X0 X1))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e81 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
          have b8e131 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e81 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e81
            | exact resolve b8e81 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e147 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e131 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e131
            | (have j0 := b8e131 (σ (k X0 X1)) (σ (M.op X1 X0))
               grind)
            | exact resolve b8e131 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e475 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e80 x y
               grind)
            | exact superpose b8e80 b8e20
            | (have j1 := b8e80 x y
               grind)
            | exact resolve b8e20 b8e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e487 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e475
               have r₂ := b8e24
               grind)
            | exact resolve b8e475 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e475
          have b8e495 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e487
               have i₂ := b8e147 y x
               grind)
            | exact superpose b8e147 b8e487
            | (have j1 := b8e147 x y
               grind)
            | (have r₁ := b8e487
               have r₂ := b8e147 y x
               grind)
            | (have r₁ := b8e487
               have r₂ := b8e147 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e487
               have r₂ := b8e147 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e487 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147 b8e487
          have b8e496 : x = y := by grind
          clear b8e495
          have b8e498 : False := by grind
          exact b8e498

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyx_y_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e31 (σ X0)
           grind)
        | exact superpose b0e31 b0e17
        | exact resolve b0e17 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e37 X0
           have i₂ := b0e31 X0
           grind)
        | exact superpose b0e31 b0e37
        | exact resolve b0e37 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e37
      have b0e98 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e40 x
           grind)
        | exact resolve b0e22 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e40
      have b0e103 : False := by grind
      exact b0e103
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e38 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y x) := by
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
        have b1e39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (k x y) = (M.op y x) := by grind
        clear b1e38
        have b1e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e39 (σ X0)
             grind)
          | exact superpose b1e39 b1e18
          | exact resolve b1e18 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e42 X0
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e42
          | exact resolve b1e42 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e42
        have b1e51 : x ≠ (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
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
        have b1e52 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e53 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e52
        have b1e54 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e53
             have r₂ := b1e21
             grind)
          | exact resolve b1e53 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e55 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e54
          | exact resolve b1e54 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e56 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e55
          | exact resolve b1e55 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e55
        have b1e65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X0 X0
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e66 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e73 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e13
          | exact resolve b1e13 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e74 : y = (M.op y x) := by
          first
          | (have i₁ := b1e73
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e73
          | exact resolve b1e73 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e67 (σ X1) (σ X0)
             grind)
          | exact superpose b1e67 b1e18
          | (have j1 := b1e67 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e24 X1 X0
             have i₂ := b1e67 (τ X1) X0
             grind)
          | exact superpose b1e67 b1e24
          | (have j1 := b1e67 (τ X1) X0
             grind)
          | exact resolve b1e24 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e67
        have b1e195 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 (σ X0) X1
             have i₂ := b1e47 X0
             grind)
          | exact superpose b1e47 b1e15
          | (have j0 := b1e15 (σ X0) X1
             grind)
          | exact resolve b1e15 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e405 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e80 X0 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e80
          | exact resolve b1e80 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e443 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e405 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e405
          | (have j0 := b1e405 X0 X1
             grind)
          | exact resolve b1e405 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e405
        have b1e609 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e79 x y
             grind)
          | exact superpose b1e79 b1e23
          | (have j1 := b1e79 x y
             grind)
          | exact resolve b1e23 b1e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e618 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e79 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79
        have b1e2930 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e609
             have i₂ := b1e443 y x
             grind)
          | exact superpose b1e443 b1e609
          | (have j1 := b1e443 (σ y) (σ x)
             grind)
          | exact resolve b1e609 b1e443
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e609
        have b1e2931 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e2930
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2930
          | exact resolve b1e2930 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2930
        have b1e2932 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b1e2931
        have b1e2937 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2932
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2932
          | exact resolve b1e2932 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2932
        have b1e2943 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e2937
             grind)
          | exact superpose b1e2937 b1e23
          | exact resolve b1e23 b1e2937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2944 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e2937
             grind)
          | exact superpose b1e2937 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e2937
             grind)
          | (have r₁ := b1e16 x x
             have r₂ := b1e2937
             grind)
          | exact resolve b1e16 b1e2937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2946 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e2944
        have b1e2948 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2946
             have i₂ := b1e47 y
             grind)
          | exact superpose b1e47 b1e2946
          | exact resolve b1e2946 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e2946
        have b1e2951 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2948
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e2948
          | exact resolve b1e2948 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2948
        have b1e2952 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2951
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e2951
          | exact resolve b1e2951 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2951
        have b1e2989 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e195 y (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e195
          | (have j0 := b1e195 y (σ x)
             grind)
          | exact resolve b1e195 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e195
        have b1e3009 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e2989
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e2989
          | exact resolve b1e2989 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2989
        have b1e10859 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e443 y x
             have i₂ := b1e2952
             grind)
          | exact superpose b1e2952 b1e443
          | (have j0 := b1e443 y x
             grind)
          | exact resolve b1e443 b1e2952
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2952
        have b1e10932 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e10859
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e10859
          | exact resolve b1e10859 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10859
        have b1e10938 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b1e10932
             have r₂ := b1e2943
             grind)
          | exact resolve b1e10932 b1e2943
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10932
        have b1e10946 : x = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e10938
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e10938
          | exact resolve b1e10938 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10938
        have b1e10947 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by grind
        clear b1e10946
        have b1e11219 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e3009
             have i₂ := b1e10947
             grind)
          | exact superpose b1e10947 b1e3009
          | (have r₁ := b1e3009
             have r₂ := b1e10947
             grind)
          | exact resolve b1e3009 b1e10947
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10947
        have b1e11271 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x x) := by grind
        clear b1e11219
        have b1e11842 : (σ x) = (σ (k y x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2937
             have i₂ := b1e11271
             grind)
          | exact superpose b1e11271 b1e2937
          | exact resolve b1e2937 b1e11271
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2937 b1e11271
        have b1e11856 : (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by grind
        clear b1e11842
        have b1e12071 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e443 y x
             have i₂ := b1e11856
             grind)
          | exact superpose b1e11856 b1e443
          | (have j0 := b1e443 y x
             grind)
          | exact resolve b1e443 b1e11856
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e443 b1e11856
        have b1e12144 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e12071
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12071
          | exact resolve b1e12071 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12071
        have b1e12150 : x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b1e12144
             have r₂ := b1e2943
             grind)
          | exact resolve b1e12144 b1e2943
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2943 b1e12144
        have b1e12158 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e12150
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12150
          | exact resolve b1e12150 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12150
        have b1e12159 : x = (M.op x x) := by grind
        clear b1e12158
        have b1e12419 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e12159
             grind)
          | exact superpose b1e12159 b1e51
          | (have r₁ := b1e51
             have r₂ := b1e12159
             grind)
          | exact resolve b1e51 b1e12159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e12428 : (M.op y x) = (M.op y y) ∨ x = (k y x) := by grind
        clear b1e12419
        have b1e12430 : x = (k y x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e12428
             have i₂ := b1e74
             grind)
          | exact superpose b1e74 b1e12428
          | exact resolve b1e12428 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12428
        have b1e12957 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e618 x y
             have i₂ := b1e12430
             grind)
          | exact superpose b1e12430 b1e618
          | (have j0 := b1e618 x y
             grind)
          | exact resolve b1e618 b1e12430
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e618 b1e12430
        have b1e12975 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
        clear b1e12957
        have b1e13702 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e12975
             grind)
          | exact superpose b1e12975 b1e23
          | exact resolve b1e23 b1e12975
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12975
        have b1e13711 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e13702
             have i₂ := b1e12159
             grind)
          | exact superpose b1e12159 b1e13702
          | exact resolve b1e13702 b1e12159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13702
        have b1e13712 : y = (M.op y y) := by grind
        clear b1e13711
        have b1e13831 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e3009
             have i₂ := b1e13712
             grind)
          | exact superpose b1e13712 b1e3009
          | exact resolve b1e3009 b1e13712
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3009
        have b1e13832 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 y X0
             have i₂ := b1e13712
             grind)
          | exact superpose b1e13712 b1e15
          | (have j0 := b1e15 y X0
             grind)
          | exact resolve b1e15 b1e13712
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13712
        have b1e13840 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
        clear b1e13831
        have b1e14156 : (σ (M.op x x)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e13840
             grind)
          | exact superpose b1e13840 b1e23
          | exact resolve b1e23 b1e13840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e13840
        have b1e14178 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e14156
             have i₂ := b1e12159
             grind)
          | exact superpose b1e12159 b1e14156
          | exact resolve b1e14156 b1e12159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14156
        have b1e15385 : y ≠ y ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e13832 x
             have i₂ := b1e74
             grind)
          | exact superpose b1e74 b1e13832
          | (have j0 := b1e13832 x
             grind)
          | (have r₁ := b1e13832 x
             have r₂ := b1e74
             grind)
          | exact resolve b1e13832 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74 b1e13832
        have b1e15390 : (M.op x y) = (k y x) := by grind
        clear b1e15385
        have b1e15392 : (M.op x x) = (k y x) := by
          first
          | (have i₁ := b1e15390
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15390
          | exact resolve b1e15390 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15390
        have b1e15393 : x = (k y x) := by
          first
          | (have i₁ := b1e15392
             have i₂ := b1e12159
             grind)
          | exact superpose b1e12159 b1e15392
          | exact resolve b1e15392 b1e12159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12159 b1e15392
        have b1e15629 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e14178
             have i₂ := b1e15393
             grind)
          | exact superpose b1e15393 b1e14178
          | exact resolve b1e14178 b1e15393
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14178 b1e15393
        have b1e15661 : False := by grind
        exact b1e15661
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b2e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e24 X0 X1
             grind)
          | exact superpose b2e24 b2e13
          | exact resolve b2e13 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e25 X1 X0
             grind)
          | exact superpose b2e25 b2e13
          | exact resolve b2e13 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e38 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y x) := by
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
        have b2e39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : (k x y) = (M.op y x) := by grind
        clear b2e38
        have b2e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e39 (σ X0)
             grind)
          | exact superpose b2e39 b2e18
          | exact resolve b2e18 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e42 X0
             have i₂ := b2e39 X0
             grind)
          | exact superpose b2e39 b2e42
          | exact resolve b2e42 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e42
        have b2e51 : x ≠ (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 y x
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e64 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e55 X0 X1
             have i₂ := b2e47 X1
             grind)
          | exact superpose b2e47 b2e55
          | (have j0 := b2e55 X0 X1
             grind)
          | exact resolve b2e55 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e66 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e29 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e29
          | exact resolve b2e29 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e62 (σ X1) (σ X0)
             grind)
          | exact superpose b2e62 b2e18
          | (have j1 := b2e62 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e83 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e24 X1 X0
             have i₂ := b2e62 (τ X1) X0
             grind)
          | exact superpose b2e62 b2e24
          | (have j1 := b2e62 (τ X1) X0
             grind)
          | exact resolve b2e24 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e89 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e35 X1 X0
             have i₂ := b2e62 (σ X1) X0
             grind)
          | exact superpose b2e62 b2e35
          | (have j1 := b2e62 (σ X1) X0
             grind)
          | exact resolve b2e35 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e62
        have b2e154 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X1) (σ X0)
             have i₂ := b2e64 X1 X0
             grind)
          | exact superpose b2e64 b2e15
          | (have j0 := b2e15 (σ X1) (σ X0)
             have j1 := b2e64 X1 X0
             grind)
          | exact resolve b2e15 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e159 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e154 X0 X1
             have i₂ := b2e47 X1
             grind)
          | exact superpose b2e47 b2e154
          | (have j0 := b2e154 X0 X1
             grind)
          | exact resolve b2e154 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e154
        have b2e169 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e159 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e159
          | (have j0 := b2e159 X0 X1
             grind)
          | exact resolve b2e159 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159
        have b2e363 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e83 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e83
          | exact resolve b2e83 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83
        have b2e401 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e363 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e363
          | (have j0 := b2e363 X0 X1
             grind)
          | exact resolve b2e363 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e363
        have b2e563 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e82 x y
             grind)
          | exact superpose b2e82 b2e23
          | (have j1 := b2e82 x y
             grind)
          | exact resolve b2e23 b2e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e572 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e82 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e962 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e169 x y
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e169
          | (have j0 := b2e169 x y
             grind)
          | exact resolve b2e169 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e169
        have b2e986 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e962
             have r₂ := b2e23
             grind)
          | exact resolve b2e962 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e962
        have b2e999 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e986
             have r₂ := b2e22
             grind)
          | exact resolve b2e986 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e986
        have b2e2309 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e89 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e89
          | exact resolve b2e89 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e2370 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e2309 X0 X1
             have i₂ := b2e66 X1 X0
             grind)
          | exact superpose b2e66 b2e2309
          | (have j0 := b2e2309 X0 X1
             grind)
          | exact resolve b2e2309 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66 b2e2309
        have b2e2490 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e563
             have i₂ := b2e401 y x
             grind)
          | exact superpose b2e401 b2e563
          | (have j1 := b2e401 (σ y) (σ x)
             grind)
          | exact resolve b2e563 b2e401
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e563
        have b2e2491 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e2490
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2490
          | exact resolve b2e2490 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2490
        have b2e2492 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b2e2491
        have b2e2497 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2492
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2492
          | exact resolve b2e2492 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2492
        have b2e2502 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e2497
             grind)
          | exact superpose b2e2497 b2e23
          | exact resolve b2e23 b2e2497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2503 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e16 (σ y) (σ x)
             have i₂ := b2e2497
             grind)
          | exact superpose b2e2497 b2e16
          | (have j0 := b2e16 (σ y) (σ x)
             grind)
          | (have r₁ := b2e16 (σ y) (σ x)
             have r₂ := b2e2497
             grind)
          | (have r₁ := b2e16 x x
             have r₂ := b2e2497
             grind)
          | exact resolve b2e16 b2e2497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2505 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e2503
        have b2e2507 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2505
             have i₂ := b2e47 y
             grind)
          | exact superpose b2e47 b2e2505
          | exact resolve b2e2505 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e2505
        have b2e2510 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2507
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e2507
          | exact resolve b2e2507 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2507
        have b2e2777 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e2370 (σ X0) (σ X1)
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e2370
          | (have j0 := b2e2370 (σ X0) (σ X1)
             grind)
          | exact resolve b2e2370 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2370
        have b2e2843 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e2777 X0 X1
             have i₂ := b2e13 (k X0 X1)
             grind)
          | exact superpose b2e13 b2e2777
          | (have j0 := b2e2777 X0 X1
             grind)
          | exact resolve b2e2777 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2777
        have b2e59030 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e2510
             grind)
          | exact superpose b2e2510 b2e22
          | exact resolve b2e22 b2e2510
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59032 : (k x y) = (τ (σ (M.op y y))) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2843 x y
             have i₂ := b2e2510
             grind)
          | exact superpose b2e2510 b2e2843
          | exact resolve b2e2843 b2e2510
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2510 b2e2843
        have b2e59093 : (k x y) = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e59032
             have i₂ := b2e13 (M.op y y)
             grind)
          | exact superpose b2e13 b2e59032
          | exact resolve b2e59032 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59032
        have b2e59124 : (k x y) = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e59093
             have r₂ := b2e59030
             grind)
          | exact resolve b2e59093 b2e59030
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59030 b2e59093
        have b2e59154 : (σ x) = (σ (k y x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e59124
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e59124
          | exact resolve b2e59124 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e59124
        have b2e61070 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e401 y x
             have i₂ := b2e59154
             grind)
          | exact superpose b2e59154 b2e401
          | (have j0 := b2e401 y x
             grind)
          | exact resolve b2e401 b2e59154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61081 : (k y x) = (τ (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e13 (k y x)
             have i₂ := b2e59154
             grind)
          | exact superpose b2e59154 b2e13
          | exact resolve b2e13 b2e59154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59154
        have b2e61249 : x = (k y x) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e61081
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e61081
          | exact resolve b2e61081 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61081
        have b2e61256 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e61070
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e61070
          | exact resolve b2e61070 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61070
        have b2e61260 : x = (k y x) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have r₁ := b2e61249
             have r₂ := b2e51
             grind)
          | exact resolve b2e61249 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e61249
        have b2e61273 : x = (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e61256
             have r₂ := b2e2502
             grind)
          | exact resolve b2e61256 b2e2502
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61256
        have b2e61277 : x = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e61273
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e61273
          | exact resolve b2e61273 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61273
        have b2e61278 : (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by grind
        clear b2e61277
        have b2e62241 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b2e572 x y
             have i₂ := b2e61260
             grind)
          | exact superpose b2e61260 b2e572
          | (have j0 := b2e572 x y
             grind)
          | exact resolve b2e572 b2e61260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e572 b2e61260
        have b2e62283 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) := by grind
        clear b2e62241
        have b2e63091 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e999
             have i₂ := b2e61278
             grind)
          | exact superpose b2e61278 b2e999
          | exact resolve b2e999 b2e61278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61278
        have b2e63112 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x x) := by grind
        clear b2e63091
        have b2e65695 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e62283
             grind)
          | exact superpose b2e62283 b2e23
          | exact resolve b2e23 b2e62283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62283
        have b2e68296 : (σ x) = (σ (k y x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2497
             have i₂ := b2e63112
             grind)
          | exact superpose b2e63112 b2e2497
          | exact resolve b2e2497 b2e63112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2497 b2e63112
        have b2e68330 : (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by grind
        clear b2e68296
        have b2e69716 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e401 y x
             have i₂ := b2e68330
             grind)
          | exact superpose b2e68330 b2e401
          | (have j0 := b2e401 y x
             grind)
          | exact resolve b2e401 b2e68330
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e401 b2e68330
        have b2e69920 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e69716
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e69716
          | exact resolve b2e69716 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69716
        have b2e69935 : x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e69920
             have r₂ := b2e2502
             grind)
          | exact resolve b2e69920 b2e2502
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2502 b2e69920
        have b2e69938 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e69935
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e69935
          | exact resolve b2e69935 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69935
        have b2e69939 : x = (M.op x x) := by grind
        clear b2e69938
        have b2e71253 : (σ x) ≠ (σ x) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b2e65695
             have i₂ := b2e69939
             grind)
          | exact superpose b2e69939 b2e65695
          | exact resolve b2e65695 b2e69939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65695
        have b2e71267 : (M.op y x) = (M.op y y) := by grind
        clear b2e71253
        have b2e72648 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e999
             have i₂ := b2e71267
             grind)
          | exact superpose b2e71267 b2e999
          | exact resolve b2e999 b2e71267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e999
        have b2e72649 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 y X0
             have i₂ := b2e71267
             grind)
          | exact superpose b2e71267 b2e15
          | (have j0 := b2e15 y X0
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e71267
             grind)
          | exact resolve b2e15 b2e71267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71267
        have b2e72669 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
        clear b2e72648
        have b2e75527 : (σ (M.op x x)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e72669
             grind)
          | exact superpose b2e72669 b2e23
          | exact resolve b2e23 b2e72669
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e72669
        have b2e75588 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e75527
             have i₂ := b2e69939
             grind)
          | exact superpose b2e69939 b2e75527
          | exact resolve b2e75527 b2e69939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75527
        have b2e82985 : (M.op x y) = (k y x) := by
          first
          | (have j0 := b2e72649 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72649
        have b2e82988 : (M.op x x) = (k y x) := by
          first
          | (have i₁ := b2e82985
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e82985
          | exact resolve b2e82985 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82985
        have b2e82990 : x = (k y x) := by
          first
          | (have i₁ := b2e82988
             have i₂ := b2e69939
             grind)
          | exact superpose b2e69939 b2e82988
          | exact resolve b2e82988 b2e69939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69939 b2e82988
        have b2e84453 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e75588
             have i₂ := b2e82990
             grind)
          | exact superpose b2e82990 b2e75588
          | exact resolve b2e75588 b2e82990
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75588 b2e82990
        have b2e84510 : False := by grind
        exact b2e84510
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
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
        have b3e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e24 X0 X1
             grind)
          | exact superpose b3e24 b3e13
          | exact resolve b3e13 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e25 X1 X0
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e38 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b3e39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b3e38
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
        have b3e43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e39 (σ X0)
             grind)
          | exact superpose b3e39 b3e18
          | exact resolve b3e18 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e43 X0
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e43
          | exact resolve b3e43 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e43
        have b3e52 : y ≠ y ∨ (M.op x y) = (M.op x x) ∨ y = (k x y) := by
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
        have b3e53 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : (M.op x y) = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e52
        have b3e55 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e53
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e53
          | exact resolve b3e53 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e56 : y = (k x y) := by
          first
          | (have r₁ := b3e54
             have r₂ := b3e20
             grind)
          | exact resolve b3e54 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e57 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e48 y
             grind)
          | exact superpose b3e48 b3e55
          | exact resolve b3e55 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e58 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e57
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e57
          | exact resolve b3e57 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e57
        have b3e59 : (σ y) = (σ (M.op y y)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e58
          | exact resolve b3e58 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e60 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b3e59
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e59
          | exact resolve b3e59 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e15 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X0 X0
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e72 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e74 (σ X1) (σ X0)
             grind)
          | exact superpose b3e74 b3e18
          | (have j1 := b3e74 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e85 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e24 X1 X0
             have i₂ := b3e74 (τ X1) X0
             grind)
          | exact superpose b3e74 b3e24
          | (have j1 := b3e74 (τ X1) X0
             grind)
          | exact resolve b3e24 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e89 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e29
          | exact resolve b3e29 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e108 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e35 X1 X0
             have i₂ := b3e74 (σ X1) X0
             grind)
          | exact superpose b3e74 b3e35
          | (have j1 := b3e74 (σ X1) X0
             grind)
          | exact resolve b3e35 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35 b3e74
        have b3e184 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e23
          | exact resolve b3e23 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e187 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 (σ X0) X1
             have i₂ := b3e48 X0
             grind)
          | exact superpose b3e48 b3e15
          | (have j0 := b3e15 (σ X0) X1
             grind)
          | exact resolve b3e15 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e380 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e85 X0 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e85
          | exact resolve b3e85 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e418 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e380 X0 X1
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e380
          | (have j0 := b3e380 X0 X1
             grind)
          | exact resolve b3e380 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e380
        have b3e575 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e84 x y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e84
          | (have j0 := b3e84 x x
             grind)
          | exact resolve b3e84 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e590 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e84 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e596 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e575
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e575
          | exact resolve b3e575 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e575
        have b3e604 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e596
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e596
          | exact resolve b3e596 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e596
        have b3e2239 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e590 (τ X1) (τ X0)
             have i₂ := b3e89 X1 X0
             grind)
          | exact superpose b3e89 b3e590
          | (have j0 := b3e590 (τ X1) (τ X0)
             grind)
          | exact resolve b3e590 b3e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89
        have b3e2244 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e590 y x
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e590
          | (have j0 := b3e590 y x
             grind)
          | exact resolve b3e590 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e590
        have b3e2253 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b3e2244
        have b3e2262 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e2239 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e2239
          | (have j0 := b3e2239 X0 X1
             grind)
          | exact resolve b3e2239 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2239
        have b3e2268 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e2262 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e2262
          | (have j0 := b3e2262 X0 X1
             grind)
          | exact resolve b3e2262 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2262
        have b3e2271 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e2268 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e2268
          | (have j0 := b3e2268 X0 X1
             grind)
          | exact resolve b3e2268 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2268
        have b3e2274 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e2271 X0 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e2271
          | (have j0 := b3e2271 X0 X1
             grind)
          | exact resolve b3e2271 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2271
        have b3e2697 : (k y (τ (σ x))) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e108 (σ x) y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e108
          | (have j0 := b3e108 (σ x) x
             grind)
          | exact resolve b3e108 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e108
        have b3e2739 : (k y (τ (σ x))) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e2697
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e2697
          | exact resolve b3e2697 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2697
        have b3e2749 : (M.op x x) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e2739
             have i₂ := b3e13 (M.op x x)
             grind)
          | exact superpose b3e13 b3e2739
          | exact resolve b3e2739 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2739
        have b3e2750 : (M.op x x) = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e2749
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e2749
          | exact resolve b3e2749 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2749
        have b3e2751 : (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
          first
          | (have i₁ := b3e2750
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e2750
          | exact resolve b3e2750 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2750
        have b3e2776 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e418 y x
             have i₂ := b3e604
             grind)
          | exact superpose b3e604 b3e418
          | (have j0 := b3e418 y x
             grind)
          | exact resolve b3e418 b3e604
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e418 b3e604
        have b3e2827 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b3e2776
             have r₂ := b3e184
             grind)
          | exact resolve b3e2776 b3e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2776
        have b3e2946 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e13 (M.op x x)
             have i₂ := b3e2827
             grind)
          | exact superpose b3e2827 b3e13
          | exact resolve b3e13 b3e2827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2827
        have b3e2997 : x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e2946
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e2946
          | exact resolve b3e2946 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2946
        have b3e3037 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e187 y (σ x)
             have i₂ := b3e2253
             grind)
          | exact superpose b3e2253 b3e187
          | (have j0 := b3e187 y (σ x)
             grind)
          | exact resolve b3e187 b3e2253
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e187 b3e2253
        have b3e3058 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e3037
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e3037
          | exact resolve b3e3037 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3037
        have b3e3074 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e3058
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e3058
          | exact resolve b3e3058 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3058
        have b3e3083 : (σ y) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e3074
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e3074
          | exact resolve b3e3074 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e3074
        have b3e3088 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e184
             have i₂ := b3e2997
             grind)
          | exact superpose b3e2997 b3e184
          | exact resolve b3e184 b3e2997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e184
        have b3e3090 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e2997
             grind)
          | exact superpose b3e2997 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e2997
             grind)
          | (have r₁ := b3e16 x x
             have r₂ := b3e2997
             grind)
          | exact resolve b3e16 b3e2997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2997
        have b3e3092 : (M.op y x) = (M.op y y) ∨ x = (k y x) ∨ x = (M.op x x) := by grind
        clear b3e3090
        have b3e3093 : x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e3092
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e3092
          | exact resolve b3e3092 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3092
        have b3e3945 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (M.op x x) = (k y x) := by
          first
          | (have i₁ := b3e3088
             have i₂ := b3e2751
             grind)
          | exact superpose b3e2751 b3e3088
          | (have r₁ := b3e3088
             have r₂ := b3e2751
             grind)
          | exact resolve b3e3088 b3e2751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2751 b3e3088
        have b3e3982 : (M.op x x) = (k y x) ∨ x = (M.op x x) := by grind
        clear b3e3945
        have b3e4915 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e3982
             have i₂ := b3e3093
             grind)
          | exact superpose b3e3093 b3e3982
          | exact resolve b3e3982 b3e3093
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3093
        have b3e4933 : y = (M.op y y) ∨ x = (M.op x x) := by grind
        clear b3e4915
        have b3e5156 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b3e15 y X0
             have i₂ := b3e4933
             grind)
          | exact superpose b3e4933 b3e15
          | (have j0 := b3e15 y X0
             grind)
          | exact resolve b3e15 b3e4933
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4933
        have b3e11822 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e5156 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e5156
          | (have j0 := b3e5156 x
             grind)
          | (have r₁ := b3e5156 x
             have r₂ := b3e21
             grind)
          | exact resolve b3e5156 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5156
        have b3e11828 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
        clear b3e11822
        have b3e12020 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e3982
             have i₂ := b3e11828
             grind)
          | exact superpose b3e11828 b3e3982
          | exact resolve b3e3982 b3e11828
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3982 b3e11828
        have b3e12028 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b3e12020
        have b3e12036 : x = (M.op x x) := by
          first
          | (have r₁ := b3e12028
             have r₂ := b3e20
             grind)
          | exact resolve b3e12028 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12028
        have b3e12300 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e12036
             grind)
          | exact superpose b3e12036 b3e60
          | exact resolve b3e60 b3e12036
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e12313 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by grind
        clear b3e12300
        have b3e12660 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e13 (k y x)
             have i₂ := b3e12313
             grind)
          | exact superpose b3e12313 b3e13
          | exact resolve b3e13 b3e12313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12313
        have b3e12728 : (σ y) = (σ (M.op y y)) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e12660
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e12660
          | exact resolve b3e12660 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12660
        have b3e13067 : (σ y) ≠ (σ y) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e3083
             have i₂ := b3e12728
             grind)
          | exact superpose b3e12728 b3e3083
          | (have r₁ := b3e3083
             have r₂ := b3e12728
             grind)
          | exact resolve b3e3083 b3e12728
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3083 b3e12728
        have b3e13114 : (σ (M.op x x)) = (σ (k y x)) ∨ x = (k y x) := by grind
        clear b3e13067
        have b3e13135 : (σ x) = (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e13114
             have i₂ := b3e12036
             grind)
          | exact superpose b3e12036 b3e13114
          | exact resolve b3e13114 b3e12036
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13114
        have b3e14041 : (k y x) = (τ (σ x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e13 (k y x)
             have i₂ := b3e13135
             grind)
          | exact superpose b3e13135 b3e13
          | exact resolve b3e13 b3e13135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13135
        have b3e14112 : x = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e14041
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e14041
          | exact resolve b3e14041 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14041
        have b3e14113 : x = (k y x) := by grind
        clear b3e14112
        have b3e14427 : x ≠ x ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e2274 y x
             have i₂ := b3e14113
             grind)
          | exact superpose b3e14113 b3e2274
          | (have j0 := b3e2274 y x
             grind)
          | (have r₁ := b3e2274 y x
             have r₂ := b3e14113
             grind)
          | exact resolve b3e2274 b3e14113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2274 b3e14113
        have b3e14431 : x = (M.op x y) := by grind
        clear b3e14427
        have b3e14655 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e14431
             grind)
          | exact superpose b3e14431 b3e20
          | exact resolve b3e20 b3e14431
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14431
        have b3e14663 : False := by grind
        exact b3e14663
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
          have b4e31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e31 (σ X0)
               grind)
            | exact superpose b4e31 b4e19
            | exact resolve b4e19 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e33
            | exact resolve b4e33 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e33
          have b4e55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e57 (σ X1) (σ X0)
               grind)
            | exact superpose b4e57 b4e19
            | (have j1 := b4e57 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X1 X0
               have i₂ := b4e57 (τ X1) X0
               grind)
            | exact superpose b4e57 b4e25
            | (have j1 := b4e57 (τ X1) X0
               grind)
            | exact resolve b4e25 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e57
          have b4e161 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) X1
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e16
            | (have j0 := b4e16 (σ X0) X1
               grind)
            | exact resolve b4e16 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e375 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
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
          have b4e413 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e375 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e375
            | (have j0 := b4e375 X0 X1
               grind)
            | exact resolve b4e375 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e375
          have b4e576 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b4e585 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e2830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e576
               have i₂ := b4e413 y x
               grind)
            | exact superpose b4e413 b4e576
            | (have j1 := b4e413 (σ y) (σ x)
               grind)
            | (have r₁ := b4e576
               have r₂ := b4e413 y x
               grind)
            | exact resolve b4e576 b4e413
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e576
          have b4e2831 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e2830
          have b4e2836 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e2831
               grind)
            | exact superpose b4e2831 b4e20
            | exact resolve b4e20 b4e2831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2837 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e2831
               grind)
            | exact superpose b4e2831 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e2831
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e2831
               grind)
            | exact resolve b4e17 b4e2831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2831
          have b4e2839 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e2837
          have b4e2841 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e2839
               have i₂ := b4e36 y
               grind)
            | exact superpose b4e36 b4e2839
            | exact resolve b4e2839 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e2839
          have b4e2845 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e2841
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e2841
            | exact resolve b4e2841 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2841
          have b4e2846 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) := by
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
          have b4e2885 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e161 y (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e161
            | (have j0 := b4e161 y (σ x)
               grind)
            | exact resolve b4e161 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e161
          have b4e2905 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e2885
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e2885
            | exact resolve b4e2885 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2885
          have b4e10116 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e413 y x
               have i₂ := b4e2846
               grind)
            | exact superpose b4e2846 b4e413
            | (have j0 := b4e413 y x
               grind)
            | exact resolve b4e413 b4e2846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2846
          have b4e10165 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by grind
          clear b4e10116
          have b4e10193 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e10165
               have r₂ := b4e2836
               grind)
            | exact resolve b4e10165 b4e2836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2836 b4e10165
          have b4e10370 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e2905
               have i₂ := b4e10193
               grind)
            | exact superpose b4e10193 b4e2905
            | (have r₁ := b4e2905
               have r₂ := b4e10193
               grind)
            | exact resolve b4e2905 b4e10193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10193
          have b4e10420 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by grind
          clear b4e10370
          have b4e10998 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e10420
               grind)
            | exact superpose b4e10420 b4e20
            | exact resolve b4e20 b4e10420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10420
          have b4e11022 : x = (M.op x y) := by
            first
            | (have j1 := b4e413 y x
               grind)
            | (have r₁ := b4e10998
               have r₂ := b4e413 y x
               grind)
            | exact resolve b4e10998 b4e413
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e413 b4e10998
          have b4e11294 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e11022
               grind)
            | exact superpose b4e11022 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e11022
               grind)
            | exact resolve b4e17 b4e11022
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e11296 : (M.op y x) = (M.op y y) ∨ x = (k y x) := by grind
          clear b4e11294
          have b4e11298 : x = (k y x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e11296
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e11296
            | exact resolve b4e11296 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11296
          have b4e11769 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e585 x y
               have i₂ := b4e11298
               grind)
            | exact superpose b4e11298 b4e585
            | (have j0 := b4e585 x y
               grind)
            | exact resolve b4e585 b4e11298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e585 b4e11298
          have b4e11787 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
          clear b4e11769
          have b4e12453 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e11787
               grind)
            | exact superpose b4e11787 b4e20
            | exact resolve b4e20 b4e11787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11787
          have b4e12461 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e12453
               have i₂ := b4e11022
               grind)
            | exact superpose b4e11022 b4e12453
            | exact resolve b4e12453 b4e11022
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12453
          have b4e12462 : y = (M.op y y) := by grind
          clear b4e12461
          have b4e12735 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e2905
               have i₂ := b4e12462
               grind)
            | exact superpose b4e12462 b4e2905
            | exact resolve b4e2905 b4e12462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2905
          have b4e12736 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e12462
               grind)
            | exact superpose b4e12462 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | exact resolve b4e16 b4e12462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12462
          have b4e12743 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
          clear b4e12735
          have b4e12946 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e12743
               grind)
            | exact superpose b4e12743 b4e20
            | exact resolve b4e20 b4e12743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12743
          have b4e12968 : (σ x) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b4e12946
               have i₂ := b4e11022
               grind)
            | exact superpose b4e11022 b4e12946
            | exact resolve b4e12946 b4e11022
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12946
          have b4e14117 : y ≠ y ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e12736 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e12736
            | (have j0 := b4e12736 x
               grind)
            | (have r₁ := b4e12736 x
               have r₂ := b4e22
               grind)
            | exact resolve b4e12736 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12736
          have b4e14122 : (M.op x y) = (k y x) := by grind
          clear b4e14117
          have b4e14124 : x = (k y x) := by
            first
            | (have i₁ := b4e14122
               have i₂ := b4e11022
               grind)
            | exact superpose b4e11022 b4e14122
            | exact resolve b4e14122 b4e11022
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11022 b4e14122
          have b4e14422 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e12968
               have i₂ := b4e14124
               grind)
            | exact superpose b4e14124 b4e12968
            | exact resolve b4e12968 b4e14124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12968 b4e14124
          have b4e14455 : False := by grind
          exact b4e14455
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e31 (σ X0)
               grind)
            | exact superpose b5e31 b5e19
            | exact resolve b5e19 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e33 X0
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e33
            | exact resolve b5e33 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e33
          have b5e39 : y ≠ y ∨ (M.op x y) = (M.op x x) ∨ y = (k x y) := by
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
          have b5e40 : (M.op x y) = (M.op x x) ∨ y = (k x y) := by grind
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
          have b5e45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e57 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e45 X0 X1
               have i₂ := b5e36 X1
               grind)
            | exact superpose b5e36 b5e45
            | (have j0 := b5e45 X0 X1
               grind)
            | exact resolve b5e45 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e133 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e808 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e133 y x
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e133
            | (have j0 := b5e133 y x
               grind)
            | exact resolve b5e133 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e133
          have b5e813 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e808
          have b5e817 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e813
               have r₂ := b5e24
               grind)
            | exact resolve b5e813 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e813
          have b5e835 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e817
               grind)
            | exact superpose b5e817 b5e23
            | exact resolve b5e23 b5e817
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e817
          have b5e842 : False := by grind
          exact b5e842
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
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
        have b6e38 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b6e39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b6e38
        have b6e41 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
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
        have b6e43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e39 (σ X0)
             grind)
          | exact superpose b6e39 b6e18
          | exact resolve b6e18 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e43 X0
             have i₂ := b6e39 X0
             grind)
          | exact superpose b6e39 b6e43
          | exact resolve b6e43 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39 b6e43
        have b6e52 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e52
          | exact resolve b6e52 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e54 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e53
             have i₂ := b6e48 y
             grind)
          | exact superpose b6e48 b6e53
          | exact resolve b6e53 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e55 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e54
          | exact resolve b6e54 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e56 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e55
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e55
          | exact resolve b6e55 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e67 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e69 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e68 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e29
          | exact resolve b6e29 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e69 (σ X1) (σ X0)
             grind)
          | exact superpose b6e69 b6e18
          | (have j1 := b6e69 (σ X1) (σ X0)
             grind)
          | exact resolve b6e18 b6e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e88 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X1 X0
             have i₂ := b6e69 (τ X1) X0
             grind)
          | exact superpose b6e69 b6e24
          | (have j1 := b6e69 (τ X1) X0
             grind)
          | exact resolve b6e24 b6e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e96 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e35 X1 X0
             have i₂ := b6e69 (σ X1) X0
             grind)
          | exact superpose b6e69 b6e35
          | (have j1 := b6e69 (σ X1) X0
             grind)
          | exact resolve b6e35 b6e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e69
        have b6e114 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e23
          | exact resolve b6e23 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e116 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 (σ X0) X1
             have i₂ := b6e48 X0
             grind)
          | exact superpose b6e48 b6e15
          | (have j0 := b6e15 (σ X0) X1
             grind)
          | exact resolve b6e15 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e415 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e88 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e88
          | exact resolve b6e88 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e455 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e415 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e415
          | (have j0 := b6e415 X0 X1
             grind)
          | exact resolve b6e415 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e415
        have b6e620 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e87 x y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e87
          | (have j0 := b6e87 x x
             grind)
          | exact resolve b6e87 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e635 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e87 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e641 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e620
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e620
          | exact resolve b6e620 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e620
        have b6e649 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e641
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e641
          | exact resolve b6e641 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e641
        have b6e1862 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e635 (τ X1) (τ X0)
             have i₂ := b6e73 X1 X0
             grind)
          | exact superpose b6e73 b6e635
          | (have j0 := b6e635 (τ X1) (τ X0)
             grind)
          | exact resolve b6e635 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73 b6e635
        have b6e1882 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e1862 X0 X1
             have i₂ := b6e14 (k X0 X1)
             grind)
          | exact superpose b6e14 b6e1862
          | (have j0 := b6e1862 X0 X1
             grind)
          | exact resolve b6e1862 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1862
        have b6e1888 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e1882 X0 X1
             have i₂ := b6e14 X1
             grind)
          | exact superpose b6e14 b6e1882
          | (have j0 := b6e1882 X0 X1
             grind)
          | exact resolve b6e1882 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1882
        have b6e1891 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e1888 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1888
          | (have j0 := b6e1888 X0 X1
             grind)
          | exact resolve b6e1888 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1888
        have b6e1894 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e1891 X0 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1891
          | (have j0 := b6e1891 X0 X1
             grind)
          | exact resolve b6e1891 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1891
        have b6e2379 : (k y (τ (σ x))) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e96 (σ x) y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e96
          | (have j0 := b6e96 (σ x) x
             grind)
          | exact resolve b6e96 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e2419 : (k y (τ (σ x))) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e2379
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e2379
          | exact resolve b6e2379 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2379
        have b6e2427 : (M.op x x) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e2419
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e2419
          | exact resolve b6e2419 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2419
        have b6e2428 : (M.op x x) = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e2427
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2427
          | exact resolve b6e2427 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2427
        have b6e2429 : (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
          first
          | (have i₁ := b6e2428
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e2428
          | exact resolve b6e2428 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2428
        have b6e2462 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e455 y x
             have i₂ := b6e649
             grind)
          | exact superpose b6e649 b6e455
          | (have j0 := b6e455 y x
             grind)
          | exact resolve b6e455 b6e649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e649
        have b6e2513 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e2462
             have r₂ := b6e114
             grind)
          | exact resolve b6e2462 b6e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2462
        have b6e2518 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e2513
             grind)
          | exact superpose b6e2513 b6e13
          | exact resolve b6e13 b6e2513
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2513
        have b6e2567 : x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e2518
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2518
          | exact resolve b6e2518 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2518
        have b6e2648 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e114
             have i₂ := b6e2567
             grind)
          | exact superpose b6e2567 b6e114
          | exact resolve b6e114 b6e2567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2650 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e2567
             grind)
          | exact superpose b6e2567 b6e16
          | (have j0 := b6e16 y x
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e2567
             grind)
          | (have r₁ := b6e16 x x
             have r₂ := b6e2567
             grind)
          | exact resolve b6e16 b6e2567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2567
        have b6e2652 : x = (k y x) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by grind
        clear b6e2650
        have b6e2690 : (σ (k x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e116 y (σ x)
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e116
          | (have j0 := b6e116 y (σ x)
             grind)
          | exact resolve b6e116 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e116
        have b6e2709 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e2690
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e2690
          | exact resolve b6e2690 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2690
        have b6e2722 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ (k x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e2709
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e2709
          | exact resolve b6e2709 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2709
        have b6e2730 : (σ (k x y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e2722
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e2722
          | exact resolve b6e2722 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48 b6e2722
        have b6e3125 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (M.op x x) = (k y x) := by
          first
          | (have i₁ := b6e2648
             have i₂ := b6e2429
             grind)
          | exact superpose b6e2429 b6e2648
          | (have r₁ := b6e2648
             have r₂ := b6e2429
             grind)
          | exact resolve b6e2648 b6e2429
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2429 b6e2648
        have b6e3162 : (M.op x x) = (k y x) ∨ x = (M.op x x) := by grind
        clear b6e3125
        have b6e7836 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e3162
             have i₂ := b6e2652
             grind)
          | exact superpose b6e2652 b6e3162
          | exact resolve b6e3162 b6e2652
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2652 b6e3162
        have b6e7857 : (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by grind
        clear b6e7836
        have b6e8049 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b6e15 y X0
             have i₂ := b6e7857
             grind)
          | exact superpose b6e7857 b6e15
          | (have j0 := b6e15 y X0
             grind)
          | (have r₁ := b6e15 y x
             have r₂ := b6e7857
             grind)
          | exact resolve b6e15 b6e7857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e13272 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e2730
             have i₂ := b6e455 x y
             grind)
          | exact superpose b6e455 b6e2730
          | (have j1 := b6e455 x y
             grind)
          | exact resolve b6e2730 b6e455
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e455
        have b6e13273 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
          first
          | (have r₁ := b6e13272
             have r₂ := b6e21
             grind)
          | exact resolve b6e13272 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13272
        have b6e20010 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e13273
             have i₂ := b6e7857
             grind)
          | exact superpose b6e7857 b6e13273
          | exact resolve b6e13273 b6e7857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7857 b6e13273
        have b6e20011 : (σ (M.op x x)) = (σ (k y x)) ∨ x = (M.op x x) := by grind
        clear b6e20010
        have b6e113076 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
          first
          | (have j0 := b6e8049 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8049
        have b6e114530 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e20011
             have i₂ := b6e113076
             grind)
          | exact superpose b6e113076 b6e20011
          | exact resolve b6e20011 b6e113076
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e20011 b6e113076
        have b6e114565 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b6e114530
        have b6e114572 : x = (M.op x x) := by
          first
          | (have r₁ := b6e114565
             have r₂ := b6e114
             grind)
          | exact resolve b6e114565 b6e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114 b6e114565
        have b6e116179 : (σ x) ≠ (σ x) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e56
             have i₂ := b6e114572
             grind)
          | exact superpose b6e114572 b6e56
          | exact resolve b6e56 b6e114572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e116218 : (σ x) = (σ (k y x)) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
        clear b6e116179
        have b6e125072 : (k y x) = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e116218
             grind)
          | exact superpose b6e116218 b6e13
          | exact resolve b6e13 b6e116218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e116218
        have b6e125376 : (σ (k x y)) = (σ (M.op y y)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e125072
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e125072
          | exact resolve b6e125072 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125072
        have b6e126254 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e2730
             have i₂ := b6e125376
             grind)
          | exact superpose b6e125376 b6e2730
          | (have r₁ := b6e2730
             have r₂ := b6e125376
             grind)
          | exact resolve b6e2730 b6e125376
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2730 b6e125376
        have b6e126548 : (σ (M.op x x)) = (σ (k y x)) ∨ x = (k y x) := by grind
        clear b6e126254
        have b6e126576 : (σ x) = (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e126548
             have i₂ := b6e114572
             grind)
          | exact superpose b6e114572 b6e126548
          | exact resolve b6e126548 b6e114572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126548
        have b6e130075 : (k y x) = (τ (σ x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e126576
             grind)
          | exact superpose b6e126576 b6e13
          | exact resolve b6e13 b6e126576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126576
        have b6e130386 : x = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e130075
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e130075
          | exact resolve b6e130075 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130075
        have b6e130387 : x = (k y x) := by grind
        clear b6e130386
        have b6e133098 : x ≠ x ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e1894 y x
             have i₂ := b6e130387
             grind)
          | exact superpose b6e130387 b6e1894
          | (have j0 := b6e1894 y x
             grind)
          | (have r₁ := b6e1894 y x
             have r₂ := b6e130387
             grind)
          | exact resolve b6e1894 b6e130387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1894 b6e130387
        have b6e133113 : x = (M.op x y) := by grind
        clear b6e133098
        have b6e133751 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e133113
             grind)
          | exact superpose b6e133113 b6e20
          | exact resolve b6e20 b6e133113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e133113
        have b6e133757 : False := by grind
        exact b6e133757
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e39 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e40 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
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
          have b7e66 : y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
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
          have b7e67 : y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e66
          have b7e69 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e22
               grind)
            | exact resolve b7e67 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e71 : False := by grind
          exact b7e71
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b8e31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e31 (σ X0)
               grind)
            | exact superpose b8e31 b8e19
            | exact resolve b8e19 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e33 X0
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e33
            | exact resolve b8e33 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e33
          have b8e45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e60 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e60 (σ X1) (σ X0)
               grind)
            | exact superpose b8e60 b8e19
            | (have j1 := b8e60 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e60 (τ X1) X0
               grind)
            | exact superpose b8e60 b8e25
            | (have j1 := b8e60 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e173 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e45 X1 X0
               have i₂ := b8e60 (σ X1) X0
               grind)
            | exact superpose b8e60 b8e45
            | (have j1 := b8e60 (σ X1) X0
               grind)
            | exact resolve b8e45 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45 b8e60
          have b8e405 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e79 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e79
            | exact resolve b8e79 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e445 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e405 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e405
            | (have j0 := b8e405 X0 X1
               grind)
            | exact resolve b8e405 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e405
          have b8e617 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e78 x y
               grind)
            | exact superpose b8e78 b8e20
            | (have j1 := b8e78 x y
               grind)
            | exact resolve b8e20 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e625 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X1) (σ X0)
               have i₂ := b8e78 X1 X0
               grind)
            | exact superpose b8e78 b8e16
            | (have j0 := b8e16 (σ X1) (σ X0)
               have j1 := b8e78 X1 X0
               grind)
            | exact resolve b8e16 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e626 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e627 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e625 X0 X1
               have i₂ := b8e36 X1
               grind)
            | exact superpose b8e36 b8e625
            | (have j0 := b8e625 X0 X1
               grind)
            | exact resolve b8e625 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e625
          have b8e635 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e627 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e627
            | (have j0 := b8e627 X0 X1
               grind)
            | exact resolve b8e627 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e627
          have b8e2273 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e173 X0 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e173
            | exact resolve b8e173 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e2331 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e2273 X0 X1
               have i₂ := b8e64 X1 X0
               grind)
            | exact superpose b8e64 b8e2273
            | (have j0 := b8e2273 X0 X1
               grind)
            | exact resolve b8e2273 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e2273
          have b8e2336 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2331 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e2331
            | (have j0 := b8e2331 (σ X0) (σ X1)
               grind)
            | exact resolve b8e2331 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2331
          have b8e2392 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2336 X0 X1
               have i₂ := b8e14 (k X0 X1)
               grind)
            | exact superpose b8e14 b8e2336
            | (have j0 := b8e2336 X0 X1
               grind)
            | exact resolve b8e2336 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2336
          have b8e2513 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e617
               have i₂ := b8e445 y x
               grind)
            | exact superpose b8e445 b8e617
            | (have j1 := b8e445 (σ y) (σ x)
               grind)
            | (have r₁ := b8e617
               have r₂ := b8e445 y x
               grind)
            | exact resolve b8e617 b8e445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e617
          have b8e2514 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e2513
          have b8e2519 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2514
               grind)
            | exact superpose b8e2514 b8e20
            | exact resolve b8e20 b8e2514
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2520 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e2514
               grind)
            | exact superpose b8e2514 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e2514
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e2514
               grind)
            | exact resolve b8e17 b8e2514
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2514
          have b8e2522 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e2520
          have b8e2524 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e2522
               have i₂ := b8e36 y
               grind)
            | exact superpose b8e36 b8e2522
            | exact resolve b8e2522 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36 b8e2522
          have b8e2528 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e2524
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e2524
            | exact resolve b8e2524 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2524
          have b8e47238 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e2528
               grind)
            | exact superpose b8e2528 b8e24
            | exact resolve b8e24 b8e2528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e47240 : (k x y) = (τ (σ (M.op y y))) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e2392 x y
               have i₂ := b8e2528
               grind)
            | exact superpose b8e2528 b8e2392
            | exact resolve b8e2392 b8e2528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2392 b8e2528
          have b8e47295 : (k x y) = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e47240
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e47240
            | exact resolve b8e47240 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47240
          have b8e47321 : (σ x) = (σ (k y x)) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e47295
               have r₂ := b8e47238
               grind)
            | exact resolve b8e47295 b8e47238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47238 b8e47295
          have b8e49878 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e445 y x
               have i₂ := b8e47321
               grind)
            | exact superpose b8e47321 b8e445
            | (have j0 := b8e445 y x
               grind)
            | exact resolve b8e445 b8e47321
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47321
          have b8e50014 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (k x y) = (M.op y y) := by grind
          clear b8e49878
          have b8e50039 : (k x y) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e50014
               have r₂ := b8e2519
               grind)
            | exact resolve b8e50014 b8e2519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2519 b8e50014
          have b8e50414 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e635 x y
               have i₂ := b8e50039
               grind)
            | exact superpose b8e50039 b8e635
            | (have j0 := b8e635 x y
               grind)
            | exact resolve b8e635 b8e50039
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e635 b8e50039
          have b8e50451 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e50414
          have b8e50483 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e50451
               have r₂ := b8e24
               grind)
            | exact resolve b8e50451 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50451
          have b8e58569 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e50483
               grind)
            | exact superpose b8e50483 b8e20
            | exact resolve b8e20 b8e50483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50483
          have b8e58630 : x = (M.op x y) := by
            first
            | (have j1 := b8e445 y x
               grind)
            | (have r₁ := b8e58569
               have r₂ := b8e445 y x
               grind)
            | exact resolve b8e58569 b8e445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e445 b8e58569
          have b8e59579 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e58630
               grind)
            | exact superpose b8e58630 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e58630
               grind)
            | exact resolve b8e17 b8e58630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e59580 : x = (k y x) ∨ (M.op y x) = (M.op y y) := by grind
          clear b8e59579
          have b8e63318 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b8e626 x y
               have i₂ := b8e59580
               grind)
            | exact superpose b8e59580 b8e626
            | (have j0 := b8e626 x y
               grind)
            | exact resolve b8e626 b8e59580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59580
          have b8e63363 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) := by grind
          clear b8e63318
          have b8e65931 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e63363
               grind)
            | exact superpose b8e63363 b8e20
            | exact resolve b8e20 b8e63363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63363
          have b8e65939 : (σ x) ≠ (σ x) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b8e65931
               have i₂ := b8e58630
               grind)
            | exact superpose b8e58630 b8e65931
            | exact resolve b8e65931 b8e58630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65931
          have b8e65940 : (M.op y x) = (M.op y y) := by grind
          clear b8e65939
          have b8e67273 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e16 y X0
               have i₂ := b8e65940
               grind)
            | exact superpose b8e65940 b8e16
            | (have j0 := b8e16 y X0
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e65940
               grind)
            | exact resolve b8e16 b8e65940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65940
          have b8e68610 : (M.op x y) = (k y x) := by
            first
            | (have j0 := b8e67273 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67273
          have b8e68613 : x = (k y x) := by
            first
            | (have i₁ := b8e68610
               have i₂ := b8e58630
               grind)
            | exact superpose b8e58630 b8e68610
            | exact resolve b8e68610 b8e58630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68610
          have b8e69988 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e626 x y
               have i₂ := b8e68613
               grind)
            | exact superpose b8e68613 b8e626
            | (have j0 := b8e626 x y
               grind)
            | exact resolve b8e626 b8e68613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e626 b8e68613
          have b8e70032 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e69988
          have b8e72749 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e70032
               grind)
            | exact superpose b8e70032 b8e20
            | exact resolve b8e20 b8e70032
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70032
          have b8e72757 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e72749
               have i₂ := b8e58630
               grind)
            | exact superpose b8e58630 b8e72749
            | exact resolve b8e72749 b8e58630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58630 b8e72749
          have b8e72758 : False := by grind
          exact b8e72758
