import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),m(X,Y)) = m(X,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxpxy_pxy_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) (M.op a b) ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a b)) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) (M.op a b) = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a b)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) (M.op a b) = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op a b)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) (M.op x y)) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op (M.op y x) (M.op x y)) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e47 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
      have b0e48 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e49 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e48
      have b0e50 : (M.op x y) = (k x y) := by grind
      clear b0e47
      have b0e51 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e49
        | exact resolve b0e49 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e52 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e51
           have i₂ := b0e50
           grind)
        | exact superpose b0e50 b0e51
        | exact resolve b0e51 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e51
      have b0e53 : False := by grind
      exact b0e53
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op (M.op y x) (M.op x y)) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ y) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by
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
        have b1e43 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b1e44 : (M.op x y) = (k x y) := by grind
        clear b1e43
        have b1e46 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e49 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e46
        have b1e51 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e49
             have r₂ := b1e23
             grind)
          | exact resolve b1e49 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e49
        have b1e52 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e51
          | exact resolve b1e51 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e53 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e44
             grind)
          | exact superpose b1e44 b1e52
          | exact resolve b1e52 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e52
        have b1e54 : False := by grind
        exact b1e54
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op (M.op y x) (M.op x y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
             have r₂ := b2e17 (M.op X1 X0) (M.op X0 X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e61 (σ X0) (σ X1)
             grind)
          | exact superpose b2e61 b2e18
          | (have j1 := b2e61 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e369 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e91 x y
             grind)
          | exact superpose b2e91 b2e19
          | (have j1 := b2e91 x y
             grind)
          | exact resolve b2e19 b2e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e383 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e369
             have r₂ := b2e22
             grind)
          | exact resolve b2e369 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e369
        have b2e387 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e383
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e383
          | exact resolve b2e383 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e383
        have b2e388 : False := by grind
        exact b2e388
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op (M.op y x) (M.op x y)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : y ≠ (M.op (M.op y x) y) := by
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
        have b3e43 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e44 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e43
        have b3e45 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b3e47 : (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e24
          | exact resolve b3e24 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e45
        have b3e51 : y ≠ y ∨ y = (M.op (M.op y x) y) ∨ y = (k x y) := by
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
        have b3e55 : y = (M.op (M.op y x) y) ∨ y = (k x y) := by grind
        clear b3e51
        have b3e57 : y = (k x y) := by
          first
          | (have r₁ := b3e55
             have r₂ := b3e23
             grind)
          | exact resolve b3e55 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e55
        have b3e73 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e47
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e47
          | exact resolve b3e47 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e57
        have b3e74 : False := by grind
        exact b3e74
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
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op (M.op y x) (M.op x y)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ (M.op (M.op y x) y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : y ≠ y ∨ y = (M.op (M.op y x) y) ∨ y = (k x y) := by
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
          have b5e52 : y = (M.op (M.op y x) y) ∨ y = (k x y) := by grind
          clear b5e51
          have b5e53 : y = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e25
               grind)
            | exact resolve b5e52 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e52
          have b5e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 (M.op X1 X0) (M.op X0 X1)
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e63 (σ X0) (σ X1)
               grind)
            | exact superpose b5e63 b5e19
            | (have j1 := b5e63 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e378 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e82 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e480 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e378 x y
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e378
            | (have j0 := b5e378 x y
               grind)
            | exact resolve b5e378 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e378
          have b5e484 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e480
          have b5e487 : False := by grind
          exact b5e487
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by grind
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
        have b6e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
             have r₂ := b6e17 (M.op X1 X0) (M.op X0 X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e79 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e63 x y
             grind)
          | exact superpose b6e63 b6e43
          | (have j1 := b6e63 x y
             grind)
          | exact resolve b6e43 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e63
        have b6e80 : y = (M.op x y) := by grind
        clear b6e79
        have b6e81 : False := by grind
        exact b6e81
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e65 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e64
          have b7e66 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e25
               grind)
            | exact resolve b7e65 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e65
          have b7e67 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e72 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e73 : y = (k x y) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e72
            | exact resolve b7e72 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 (M.op X1 X0) (M.op X0 X1)
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e86 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e86 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e97 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e87 x y
               grind)
            | exact superpose b7e87 b7e73
            | (have j1 := b7e87 x y
               grind)
            | exact resolve b7e73 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e87
          have b7e99 : y = (M.op x y) := by grind
          clear b7e97
          have b7e102 : False := by grind
          exact b7e102
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e72 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
               have r₂ := b8e18 (M.op X1 X0) (M.op X0 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e78 (σ X0) (σ X1)
               grind)
            | exact superpose b8e78 b8e19
            | (have j1 := b8e78 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e86 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e78 (τ X0) X1
               grind)
            | exact superpose b8e78 b8e25
            | (have j1 := b8e78 (τ X0) X1
               grind)
            | exact resolve b8e25 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e78
          have b8e178 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e86 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e86
            | exact resolve b8e86 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e178 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e178
            | (have j0 := b8e178 X0 X1
               grind)
            | exact resolve b8e178 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e178
          have b8e316 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          clear b8e84
          have b8e330 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e316
               have r₂ := b8e24
               grind)
            | exact resolve b8e316 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e316
          have b8e335 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e330
               have i₂ := b8e201 x y
               grind)
            | exact superpose b8e201 b8e330
            | (have j1 := b8e201 x y
               grind)
            | (have r₁ := b8e330
               have r₂ := b8e201 x y
               grind)
            | exact resolve b8e330 b8e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e201 b8e330
          have b8e336 : y = (M.op x y) := by grind
          clear b8e335
          have b8e338 : False := by grind
          exact b8e338

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),m(Y,X)) = m(X,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxpyx_pxy_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) (M.op b a) ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b a)) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) (M.op b a) = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b a)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) (M.op b a) = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b a)) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) (M.op y x)) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op (M.op y x) (M.op y x)) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e45 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
      have b0e46 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op (M.op y x) (M.op y x)) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ y) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) := by
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
        have b1e44 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e46 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
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
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op (M.op y x) (M.op y x)) := by grind
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
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
             have r₂ := b2e17 (M.op X1 X1) (M.op X1 X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
             have i₂ := b2e56 (σ X0) (σ X1)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e369 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
        have b2e381 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e369
             have r₂ := b2e22
             grind)
          | exact resolve b2e369 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e369
        have b2e384 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e381
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e381
          | exact resolve b2e381 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e381
        have b2e385 : False := by grind
        exact b2e385
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op (M.op y x) (M.op y x)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : y ≠ (M.op (M.op y x) (M.op y x)) := by
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
        have b3e47 : y ≠ y ∨ y = (M.op (M.op y x) (M.op y x)) ∨ y = (k x y) := by
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
        have b3e50 : y = (M.op (M.op y x) (M.op y x)) ∨ y = (k x y) := by grind
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
        have b3e71 : (σ y) ≠ (σ y) := by
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
        have b3e72 : False := by grind
        exact b3e72
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
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op (M.op y x) (M.op y x)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ (M.op (M.op y x) (M.op y x)) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : y ≠ y ∨ y = (M.op (M.op y x) (M.op y x)) ∨ y = (k x y) := by
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
          have b5e51 : y = (M.op (M.op y x) (M.op y x)) ∨ y = (k x y) := by grind
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
          have b5e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
               have r₂ := b5e18 (M.op X1 X1) (M.op X1 X1)
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e61 (σ X0) (σ X1)
               grind)
            | exact superpose b5e61 b5e19
            | (have j1 := b5e61 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e376 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e80 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e476 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e376 x y
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e376
            | (have j0 := b5e376 x y
               grind)
            | exact resolve b5e376 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e376
          have b5e480 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e476
          have b5e483 : False := by grind
          exact b5e483
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) := by grind
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
        have b6e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
             have r₂ := b6e17 (M.op X1 X1) (M.op X1 X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e76 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e57 x y
             grind)
          | exact superpose b6e57 b6e41
          | (have j1 := b6e57 x y
             grind)
          | exact resolve b6e41 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e57
        have b6e77 : y = (M.op x y) := by grind
        clear b6e76
        have b6e78 : False := by grind
        exact b6e78
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e64 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e63
          have b7e65 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e25
               grind)
            | exact resolve b7e64 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e64
          have b7e66 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e71 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e14
            | exact resolve b7e14 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e72 : y = (k x y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e71
            | exact resolve b7e71 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
               have r₂ := b7e18 (M.op X1 X1) (M.op X1 X1)
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e84 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e84 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e95 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e85 x y
               grind)
            | exact superpose b7e85 b7e72
            | (have j1 := b7e85 x y
               grind)
            | exact resolve b7e72 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e85
          have b7e97 : y = (M.op x y) := by grind
          clear b7e95
          have b7e100 : False := by grind
          exact b7e100
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e72 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
               have r₂ := b8e18 (M.op X1 X1) (M.op X1 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e75 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e76 (σ X0) (σ X1)
               grind)
            | exact superpose b8e76 b8e19
            | (have j1 := b8e76 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e76 (τ X0) X1
               grind)
            | exact superpose b8e76 b8e25
            | (have j1 := b8e76 (τ X0) X1
               grind)
            | exact resolve b8e25 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e76
          have b8e181 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
          have b8e204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e181 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e181
            | (have j0 := b8e181 X0 X1
               grind)
            | exact resolve b8e181 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181
          have b8e318 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e82 x y
               grind)
            | exact superpose b8e82 b8e20
            | (have j1 := b8e82 x y
               grind)
            | exact resolve b8e20 b8e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e330 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e318
               have r₂ := b8e24
               grind)
            | exact resolve b8e318 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e318
          have b8e334 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e330
               have i₂ := b8e204 x y
               grind)
            | exact superpose b8e204 b8e330
            | (have j1 := b8e204 x y
               grind)
            | (have r₁ := b8e330
               have r₂ := b8e204 x y
               grind)
            | exact resolve b8e330 b8e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e204 b8e330
          have b8e335 : y = (M.op x y) := by grind
          clear b8e334
          have b8e337 : False := by grind
          exact b8e337

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),m(Y,X)) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxpyx_pyy_pyx_y_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) (M.op b a) ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b a)) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) (M.op b a) = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b a)) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) (M.op b a) = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b a)) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) (M.op y x)) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op y x) (M.op y x)) = (M.op y y) := by grind
      have b0e20 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e45 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) := by
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
      have b0e46 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op y x) (M.op y x)) = (M.op y y) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
             have r₂ := b2e17 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e380 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
        have b2e397 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e380
             have r₂ := b2e22
             grind)
          | exact resolve b2e380 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e380
        have b2e404 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e397
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e397
          | exact resolve b2e397 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e397
        have b2e405 : False := by grind
        exact b2e405
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e20 : (M.op (M.op y x) (M.op y x)) ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e23 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        · have b5e21 : (M.op (M.op y x) (M.op y x)) ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
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
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) = (M.op (σ y) (σ y)) := by grind
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
        have b6e51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
             have r₂ := b6e17 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e74 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e55 y x
             grind)
          | exact superpose b6e55 b6e41
          | (have j1 := b6e55 y x
             grind)
          | exact resolve b6e41 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e55
        have b6e75 : y = (M.op y x) := by grind
        clear b6e74
        have b6e76 : False := by grind
        exact b6e76
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
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
          have b8e72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
               have r₂ := b8e18 (M.op X0 X0) (M.op X0 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e76 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e75 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b8e84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
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
          have b8e180 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
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
          have b8e203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e180 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e180
            | (have j0 := b8e180 X0 X1
               grind)
            | exact resolve b8e180 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180
          have b8e331 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e82 x y
               grind)
            | exact superpose b8e82 b8e20
            | (have j1 := b8e82 x y
               grind)
            | exact resolve b8e20 b8e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e348 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e331
               have r₂ := b8e24
               grind)
            | exact resolve b8e331 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e331
          have b8e362 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e348
               have i₂ := b8e203 x y
               grind)
            | exact superpose b8e203 b8e348
            | (have j1 := b8e203 x y
               grind)
            | (have r₁ := b8e348
               have r₂ := b8e203 x y
               grind)
            | exact resolve b8e348 b8e203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203 b8e348
          have b8e363 : y = (M.op y x) := by grind
          clear b8e362
          have b8e365 : False := by grind
          exact b8e365

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),m(Y,Y)) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxpyy_x_pyx_x_pyx_x_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) (M.op b b) ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b b)) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) (M.op b b) = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b b)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) (M.op b b) = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) (M.op b b)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) (M.op y y)) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        | (have r₁ := b0e14 (M.op X1 X1) X1
           have r₂ := b0e16 (M.op X1 X1) (M.op X1 (M.op X1 X1))
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e56 X1 (τ X0)
           grind)
        | exact superpose b0e56 b0e22
        | (have j1 := b0e56 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e56 (σ X1) (σ X0)
           grind)
        | exact superpose b0e56 b0e17
        | (have j1 := b0e56 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e285 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
      have b0e312 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e285 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e285
        | (have j0 := b0e285 X0 X1
           grind)
        | exact resolve b0e285 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e285
      have b0e447 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
      have b0e463 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e71 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71
      have b0e625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e447
           have i₂ := b0e312 x y
           grind)
        | exact superpose b0e312 b0e447
        | (have j1 := b0e312 (σ x) (σ y)
           grind)
        | (have r₁ := b0e447
           have r₂ := b0e312 x y
           grind)
        | exact resolve b0e447 b0e312
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e447
      have b0e626 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e625
      have b0e629 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e626
           grind)
        | exact superpose b0e626 b0e18
        | exact resolve b0e18 b0e626
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e630 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e626
           grind)
        | exact superpose b0e626 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e626
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e626
           grind)
        | exact resolve b0e15 b0e626
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e631 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e626
           grind)
        | exact superpose b0e626 b0e14
        | exact resolve b0e14 b0e626
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e626
      have b0e632 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
      clear b0e630
      have b0e633 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e631
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e631
        | exact resolve b0e631 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e631
      have b0e634 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e632
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e632
        | exact resolve b0e632 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e632
      have b0e636 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e634
           have r₂ := b0e633
           grind)
        | exact resolve b0e634 b0e633
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e633 b0e634
      have b0e719 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e312 x y
           have i₂ := b0e636
           grind)
        | exact superpose b0e636 b0e312
        | (have j0 := b0e312 x y
           grind)
        | exact resolve b0e312 b0e636
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e312 b0e636
      have b0e743 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e719
      have b0e764 : y = (M.op x y) := by
        first
        | (have r₁ := b0e743
           have r₂ := b0e629
           grind)
        | exact resolve b0e743 b0e629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e629 b0e743
      have b0e836 : y ≠ y ∨ y = (M.op y (M.op x x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e764
           grind)
        | exact superpose b0e764 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e764
           grind)
        | exact resolve b0e15 b0e764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e837 : y ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e764
           grind)
        | exact superpose b0e764 b0e14
        | exact resolve b0e14 b0e764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e838 : y = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
      clear b0e836
      have b0e839 : y = (k y x) := by
        first
        | (have r₁ := b0e838
           have r₂ := b0e837
           grind)
        | exact resolve b0e838 b0e837
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e837 b0e838
      have b0e919 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e463 x y
           have i₂ := b0e839
           grind)
        | exact superpose b0e839 b0e463
        | (have j0 := b0e463 x y
           grind)
        | exact resolve b0e463 b0e839
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e463 b0e839
      have b0e923 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e919
      have b0e1006 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e923
           grind)
        | exact superpose b0e923 b0e18
        | exact resolve b0e18 b0e923
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e923
      have b0e1012 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e1006
           have i₂ := b0e764
           grind)
        | exact superpose b0e764 b0e1006
        | exact resolve b0e1006 b0e764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e764 b0e1006
      have b0e1013 : False := by grind
      exact b0e1013
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b1e57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          | (have r₁ := b1e15 (M.op X1 X1) X1
             have r₂ := b1e17 (M.op X1 X1) (M.op X1 (M.op X1 X1))
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e73 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e25 X0 X1
             have i₂ := b1e62 X1 (τ X0)
             grind)
          | exact superpose b1e62 b1e25
          | (have j1 := b1e62 X1 (τ X0)
             grind)
          | exact resolve b1e25 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e62 (σ X1) (σ X0)
             grind)
          | exact superpose b1e62 b1e18
          | (have j1 := b1e62 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e266 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e73 (σ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e73
          | exact resolve b1e73 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e291 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e266 X0 X1
             have i₂ := b1e18 X1 X0
             grind)
          | exact superpose b1e18 b1e266
          | (have j0 := b1e266 X0 X1
             grind)
          | exact resolve b1e266 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e266
        have b1e420 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e74 x y
             grind)
          | exact superpose b1e74 b1e19
          | (have j1 := b1e74 x y
             grind)
          | exact resolve b1e19 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e429 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e74 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e615 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e420
             have i₂ := b1e291 x y
             grind)
          | exact superpose b1e291 b1e420
          | (have j1 := b1e291 (σ x) (σ y)
             grind)
          | (have r₁ := b1e420
             have r₂ := b1e291 x y
             grind)
          | exact resolve b1e420 b1e291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e420
        have b1e616 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b1e615
        have b1e619 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e616
             grind)
          | exact superpose b1e616 b1e19
          | exact resolve b1e19 b1e616
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e620 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e616
             grind)
          | exact superpose b1e616 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e616
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e616
             grind)
          | exact resolve b1e16 b1e616
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e621 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e616
             grind)
          | exact superpose b1e616 b1e15
          | exact resolve b1e15 b1e616
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e616
        have b1e622 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b1e620
        have b1e623 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e621
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e621
          | exact resolve b1e621 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e621
        have b1e624 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e622
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e622
          | exact resolve b1e622 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e622
        have b1e626 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b1e624
             have r₂ := b1e623
             grind)
          | exact resolve b1e624 b1e623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e623 b1e624
        have b1e696 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e291 x y
             have i₂ := b1e626
             grind)
          | exact superpose b1e626 b1e291
          | (have j0 := b1e291 x y
             grind)
          | exact resolve b1e291 b1e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e291 b1e626
        have b1e719 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b1e696
        have b1e740 : y = (M.op x y) := by
          first
          | (have r₁ := b1e719
             have r₂ := b1e619
             grind)
          | exact resolve b1e719 b1e619
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e619 b1e719
        have b1e810 : y ≠ y ∨ y = (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e740
             grind)
          | exact superpose b1e740 b1e16
          | (have j0 := b1e16 y x
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e740
             grind)
          | exact resolve b1e16 b1e740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e811 : y ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e740
             grind)
          | exact superpose b1e740 b1e15
          | exact resolve b1e15 b1e740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e812 : y = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
        clear b1e810
        have b1e813 : y = (k y x) := by
          first
          | (have r₁ := b1e812
             have r₂ := b1e811
             grind)
          | exact resolve b1e812 b1e811
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e811 b1e812
        have b1e891 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e429 x y
             have i₂ := b1e813
             grind)
          | exact superpose b1e813 b1e429
          | (have j0 := b1e429 x y
             grind)
          | exact resolve b1e429 b1e813
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e429 b1e813
        have b1e895 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b1e891
        have b1e977 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e895
             grind)
          | exact superpose b1e895 b1e19
          | exact resolve b1e19 b1e895
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e895
        have b1e983 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e977
             have i₂ := b1e740
             grind)
          | exact superpose b1e740 b1e977
          | exact resolve b1e977 b1e740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e740 b1e977
        have b1e984 : False := by grind
        exact b1e984
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b2e53 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          | (have r₁ := b2e15 (M.op X1 X1) X1
             have r₂ := b2e17 (M.op X1 X1) (M.op X1 (M.op X1 X1))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
             have i₂ := b2e58 X1 (τ X0)
             grind)
          | exact superpose b2e58 b2e24
          | (have j1 := b2e58 X1 (τ X0)
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
        have b2e411 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
        have b2e420 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e77 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e411
             have i₂ := b2e277 x y
             grind)
          | exact superpose b2e277 b2e411
          | (have j1 := b2e277 (σ x) (σ y)
             grind)
          | (have r₁ := b2e411
             have r₂ := b2e277 x y
             grind)
          | exact resolve b2e411 b2e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e411
        have b2e546 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b2e545
        have b2e622 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e546
             grind)
          | exact superpose b2e546 b2e19
          | exact resolve b2e19 b2e546
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e623 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e16 (σ y) (σ x)
             have i₂ := b2e546
             grind)
          | exact superpose b2e546 b2e16
          | (have j0 := b2e16 (σ y) (σ x)
             grind)
          | (have r₁ := b2e16 (σ y) (σ x)
             have r₂ := b2e546
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e546
             grind)
          | exact resolve b2e16 b2e546
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e624 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e15 (σ y) (σ x)
             have i₂ := b2e546
             grind)
          | exact superpose b2e546 b2e15
          | exact resolve b2e15 b2e546
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e546
        have b2e625 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b2e623
        have b2e626 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e624
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e624
          | exact resolve b2e624 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e624
        have b2e627 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e625
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e625
          | exact resolve b2e625 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e625
        have b2e629 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b2e627
             have r₂ := b2e626
             grind)
          | exact resolve b2e627 b2e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e626 b2e627
        have b2e774 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e277 x y
             have i₂ := b2e629
             grind)
          | exact superpose b2e629 b2e277
          | (have j0 := b2e277 x y
             grind)
          | exact resolve b2e277 b2e629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277 b2e629
        have b2e797 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b2e774
        have b2e818 : y = (M.op x y) := by
          first
          | (have r₁ := b2e797
             have r₂ := b2e622
             grind)
          | exact resolve b2e797 b2e622
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e622 b2e797
        have b2e900 : y ≠ y ∨ y = (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e818
             grind)
          | exact superpose b2e818 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e818
             grind)
          | exact resolve b2e16 b2e818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e901 : y ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e818
             grind)
          | exact superpose b2e818 b2e15
          | exact resolve b2e15 b2e818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e902 : y = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
        clear b2e900
        have b2e903 : y = (k y x) := by
          first
          | (have r₁ := b2e902
             have r₂ := b2e901
             grind)
          | exact resolve b2e902 b2e901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e901 b2e902
        have b2e995 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e420 x y
             have i₂ := b2e903
             grind)
          | exact superpose b2e903 b2e420
          | (have j0 := b2e420 x y
             grind)
          | exact resolve b2e420 b2e903
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e420 b2e903
        have b2e999 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e995
        have b2e1095 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e999
             grind)
          | exact superpose b2e999 b2e19
          | exact resolve b2e19 b2e999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e999
        have b2e1101 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1095
             have i₂ := b2e818
             grind)
          | exact superpose b2e818 b2e1095
          | exact resolve b2e1095 b2e818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e818 b2e1095
        have b2e1102 : False := by grind
        exact b2e1102
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b3e58 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          | (have r₁ := b3e15 (M.op X1 X1) X1
             have r₂ := b3e17 (M.op X1 X1) (M.op X1 (M.op X1 X1))
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e63 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e78 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e25 X0 X1
             have i₂ := b3e63 X1 (τ X0)
             grind)
          | exact superpose b3e63 b3e25
          | (have j1 := b3e63 X1 (τ X0)
             grind)
          | exact resolve b3e25 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e63 (σ X1) (σ X0)
             grind)
          | exact superpose b3e63 b3e18
          | (have j1 := b3e63 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e273 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e78 (σ X0) X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e78
          | exact resolve b3e78 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e298 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e273 X0 X1
             have i₂ := b3e18 X1 X0
             grind)
          | exact superpose b3e18 b3e273
          | (have j0 := b3e273 X0 X1
             grind)
          | exact resolve b3e273 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e273
        have b3e423 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e80 x y
             grind)
          | exact superpose b3e80 b3e19
          | (have j1 := b3e80 x y
             grind)
          | exact resolve b3e19 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e439 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e80 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e423
             have i₂ := b3e298 x y
             grind)
          | exact superpose b3e298 b3e423
          | (have j1 := b3e298 (σ x) (σ y)
             grind)
          | (have r₁ := b3e423
             have r₂ := b3e298 x y
             grind)
          | exact resolve b3e423 b3e298
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e423
        have b3e652 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b3e651
        have b3e655 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e652
             grind)
          | exact superpose b3e652 b3e19
          | exact resolve b3e19 b3e652
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e656 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e652
             grind)
          | exact superpose b3e652 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | (have r₁ := b3e16 (σ y) (σ x)
             have r₂ := b3e652
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e652
             grind)
          | exact resolve b3e16 b3e652
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e657 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e652
             grind)
          | exact superpose b3e652 b3e15
          | exact resolve b3e15 b3e652
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e652
        have b3e658 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b3e656
        have b3e659 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e657
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e657
          | exact resolve b3e657 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e657
        have b3e660 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e658
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e658
          | exact resolve b3e658 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e658
        have b3e662 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b3e660
             have r₂ := b3e659
             grind)
          | exact resolve b3e660 b3e659
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e659 b3e660
        have b3e744 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e298 x y
             have i₂ := b3e662
             grind)
          | exact superpose b3e662 b3e298
          | (have j0 := b3e298 x y
             grind)
          | exact resolve b3e298 b3e662
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e298 b3e662
        have b3e767 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b3e744
        have b3e788 : y = (M.op x y) := by
          first
          | (have r₁ := b3e767
             have r₂ := b3e655
             grind)
          | exact resolve b3e767 b3e655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e655 b3e767
        have b3e859 : y ≠ y ∨ y = (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e788
             grind)
          | exact superpose b3e788 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e788
             grind)
          | exact resolve b3e16 b3e788
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e860 : y ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e788
             grind)
          | exact superpose b3e788 b3e15
          | exact resolve b3e15 b3e788
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e861 : y = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
        clear b3e859
        have b3e862 : y = (k y x) := by
          first
          | (have r₁ := b3e861
             have r₂ := b3e860
             grind)
          | exact resolve b3e861 b3e860
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e860 b3e861
        have b3e941 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e439 x y
             have i₂ := b3e862
             grind)
          | exact superpose b3e862 b3e439
          | (have j0 := b3e439 x y
             grind)
          | exact resolve b3e439 b3e862
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e439 b3e862
        have b3e945 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b3e941
        have b3e1027 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e945
             grind)
          | exact superpose b3e945 b3e19
          | exact resolve b3e19 b3e945
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e945
        have b3e1033 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e1027
             have i₂ := b3e788
             grind)
          | exact superpose b3e788 b3e1027
          | exact resolve b3e1027 b3e788
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e788 b3e1027
        have b3e1034 : False := by grind
        exact b3e1034
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b4e52 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b4e16 (M.op X1 X1) X1
               have r₂ := b4e18 (M.op X1 X1) (M.op X1 (M.op X1 X1))
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e56 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e57 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e69 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e57 X1 (τ X0)
               grind)
            | exact superpose b4e57 b4e28
            | (have j1 := b4e57 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          clear b4e57
          have b4e196 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e69 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e69
            | exact resolve b4e69 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e196 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e196
            | (have j0 := b4e196 X0 X1
               grind)
            | exact resolve b4e196 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e196
          have b4e336 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e71 x y
               grind)
            | exact superpose b4e71 b4e20
            | (have j1 := b4e71 x y
               grind)
            | exact resolve b4e20 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e345 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e568 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e336
               have i₂ := b4e219 x y
               grind)
            | exact superpose b4e219 b4e336
            | (have j1 := b4e219 (σ x) (σ y)
               grind)
            | (have r₁ := b4e336
               have r₂ := b4e219 x y
               grind)
            | exact resolve b4e336 b4e219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e336
          have b4e569 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b4e568
          have b4e572 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e569
               grind)
            | exact superpose b4e569 b4e20
            | exact resolve b4e20 b4e569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e573 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e569
               grind)
            | exact superpose b4e569 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e569
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e569
               grind)
            | exact resolve b4e17 b4e569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e574 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e569
               grind)
            | exact superpose b4e569 b4e16
            | exact resolve b4e16 b4e569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e569
          have b4e575 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b4e573
          have b4e576 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e574
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e574
            | exact resolve b4e574 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e574
          have b4e577 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e575
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e575
            | exact resolve b4e575 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e575
          have b4e579 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e577
               have r₂ := b4e576
               grind)
            | exact resolve b4e577 b4e576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e576 b4e577
          have b4e650 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e219 x y
               have i₂ := b4e579
               grind)
            | exact superpose b4e579 b4e219
            | (have j0 := b4e219 x y
               grind)
            | exact resolve b4e219 b4e579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e219 b4e579
          have b4e674 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b4e650
          have b4e695 : y = (M.op x y) := by
            first
            | (have r₁ := b4e674
               have r₂ := b4e572
               grind)
            | exact resolve b4e674 b4e572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e572 b4e674
          have b4e766 : y ≠ y ∨ y = (M.op y (M.op x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e695
               grind)
            | exact superpose b4e695 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e695
               grind)
            | exact resolve b4e17 b4e695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e767 : y ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e695
               grind)
            | exact superpose b4e695 b4e16
            | exact resolve b4e16 b4e695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e768 : y = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
          clear b4e766
          have b4e769 : y = (k y x) := by
            first
            | (have r₁ := b4e768
               have r₂ := b4e767
               grind)
            | exact resolve b4e768 b4e767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e767 b4e768
          have b4e848 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e345 x y
               have i₂ := b4e769
               grind)
            | exact superpose b4e769 b4e345
            | (have j0 := b4e345 x y
               grind)
            | exact resolve b4e345 b4e769
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e345 b4e769
          have b4e852 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b4e848
          have b4e935 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e852
               grind)
            | exact superpose b4e852 b4e20
            | exact resolve b4e20 b4e852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e852
          have b4e941 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e935
               have i₂ := b4e695
               grind)
            | exact superpose b4e695 b4e935
            | exact resolve b4e935 b4e695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e695 b4e935
          have b4e942 : False := by grind
          exact b4e942
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op (M.op y x) (M.op y y)) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : x ≠ x ∨ x = (M.op x (M.op y y)) ∨ x = (k x y) := by
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
          have b5e42 : x = (M.op x (M.op y y)) ∨ x = (k x y) := by grind
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
          have b5e47 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b5e16 (M.op X1 X1) X1
               have r₂ := b5e18 (M.op X1 X1) (M.op X1 (M.op X1 X1))
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e52 (σ X1) (σ X0)
               grind)
            | exact superpose b5e52 b5e19
            | (have j1 := b5e52 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e342 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e67 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e481 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e342 y x
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e342
            | (have j0 := b5e342 y x
               grind)
            | exact resolve b5e342 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e342
          have b5e485 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e481
          have b5e488 : False := by grind
          exact b5e488
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e60 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          | (have r₁ := b6e15 (M.op X1 X1) X1
             have r₂ := b6e17 (M.op X1 X1) (M.op X1 (M.op X1 X1))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e65 (σ X1) (σ X0)
             grind)
          | exact superpose b6e65 b6e18
          | (have j1 := b6e65 (σ X1) (σ X0)
             grind)
          | exact resolve b6e18 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e86 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X0 X1
             have i₂ := b6e65 X1 (τ X0)
             grind)
          | exact superpose b6e65 b6e24
          | (have j1 := b6e65 X1 (τ X0)
             grind)
          | exact resolve b6e24 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e65
        have b6e221 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e86 (σ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e86
          | exact resolve b6e86 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e244 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e221 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e221
          | (have j0 := b6e221 X0 X1
             grind)
          | exact resolve b6e221 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e221
        have b6e363 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e83 x y
             grind)
          | exact superpose b6e83 b6e19
          | (have j1 := b6e83 x y
             grind)
          | exact resolve b6e19 b6e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e379 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e83 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e622 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e363
             have i₂ := b6e244 x y
             grind)
          | exact superpose b6e244 b6e363
          | (have j1 := b6e244 (σ x) (σ y)
             grind)
          | (have r₁ := b6e363
             have r₂ := b6e244 x y
             grind)
          | exact resolve b6e363 b6e244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e363
        have b6e623 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b6e622
        have b6e626 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e623
             grind)
          | exact superpose b6e623 b6e19
          | exact resolve b6e19 b6e623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e627 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e623
             grind)
          | exact superpose b6e623 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e623
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e623
             grind)
          | exact resolve b6e16 b6e623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e628 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e623
             grind)
          | exact superpose b6e623 b6e15
          | exact resolve b6e15 b6e623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e623
        have b6e629 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b6e627
        have b6e630 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e628
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e628
          | exact resolve b6e628 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e628
        have b6e631 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e629
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e629
          | exact resolve b6e629 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e629
        have b6e633 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e631
             have r₂ := b6e630
             grind)
          | exact resolve b6e631 b6e630
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e630 b6e631
        have b6e716 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e244 x y
             have i₂ := b6e633
             grind)
          | exact superpose b6e633 b6e244
          | (have j0 := b6e244 x y
             grind)
          | exact resolve b6e244 b6e633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e244 b6e633
        have b6e739 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b6e716
        have b6e760 : y = (M.op x y) := by
          first
          | (have r₁ := b6e739
             have r₂ := b6e626
             grind)
          | exact resolve b6e739 b6e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e626 b6e739
        have b6e831 : y ≠ y ∨ y = (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e760
             grind)
          | exact superpose b6e760 b6e16
          | (have j0 := b6e16 y x
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e760
             grind)
          | exact resolve b6e16 b6e760
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e832 : y ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e760
             grind)
          | exact superpose b6e760 b6e15
          | exact resolve b6e15 b6e760
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e833 : y = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
        clear b6e831
        have b6e834 : y = (k y x) := by
          first
          | (have r₁ := b6e833
             have r₂ := b6e832
             grind)
          | exact resolve b6e833 b6e832
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e832 b6e833
        have b6e913 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e379 x y
             have i₂ := b6e834
             grind)
          | exact superpose b6e834 b6e379
          | (have j0 := b6e379 x y
             grind)
          | exact resolve b6e379 b6e834
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e379 b6e834
        have b6e917 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b6e913
        have b6e999 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e917
             grind)
          | exact superpose b6e917 b6e19
          | exact resolve b6e19 b6e917
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e917
        have b6e1005 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b6e999
             have i₂ := b6e760
             grind)
          | exact superpose b6e760 b6e999
          | exact resolve b6e999 b6e760
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e760 b6e999
        have b6e1006 : False := by grind
        exact b6e1006
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ y))) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (M.op (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e43 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e25
               grind)
            | exact resolve b7e42 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e42
          have b7e44 : (σ x) = (σ (k x y)) := by
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
          have b7e47 : (k x y) = (τ (σ x)) := by
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
          have b7e48 : x = (k x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e47
            | exact resolve b7e47 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e54 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b7e16 (M.op X1 X1) X1
               have r₂ := b7e18 (M.op X1 X1) (M.op X1 (M.op X1 X1))
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e67 : x = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e59 x y
               grind)
            | exact superpose b7e59 b7e48
            | (have j1 := b7e59 x y
               grind)
            | exact resolve b7e48 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e59
          have b7e69 : x = (M.op y x) := by grind
          clear b7e67
          have b7e72 : False := by grind
          exact b7e72
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b8e16 (M.op X1 X1) X1
               have r₂ := b8e18 (M.op X1 X1) (M.op X1 (M.op X1 X1))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e76 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e56 X1 (τ X0)
               grind)
            | exact superpose b8e56 b8e26
            | (have j1 := b8e56 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e56
          have b8e213 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
          have b8e238 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e213 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e213
            | (have j0 := b8e213 X0 X1
               grind)
            | exact resolve b8e213 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e213
          have b8e363 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e73 x y
               grind)
            | exact superpose b8e73 b8e20
            | (have j1 := b8e73 x y
               grind)
            | exact resolve b8e20 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e372 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e363
               have i₂ := b8e238 x y
               grind)
            | exact superpose b8e238 b8e363
            | (have j1 := b8e238 (σ x) (σ y)
               grind)
            | (have r₁ := b8e363
               have r₂ := b8e238 x y
               grind)
            | exact resolve b8e363 b8e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e363
          have b8e551 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b8e550
          have b8e554 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e551
               grind)
            | exact superpose b8e551 b8e20
            | exact resolve b8e20 b8e551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e555 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e551
               grind)
            | exact superpose b8e551 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e551
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e551
               grind)
            | exact resolve b8e17 b8e551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e556 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e551
               grind)
            | exact superpose b8e551 b8e16
            | exact resolve b8e16 b8e551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e551
          have b8e557 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e555
          have b8e558 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e556
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e556
            | exact resolve b8e556 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e556
          have b8e559 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e557
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e557
            | exact resolve b8e557 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e557
          have b8e561 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e559
               have r₂ := b8e558
               grind)
            | exact resolve b8e559 b8e558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e558 b8e559
          have b8e694 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e238 x y
               have i₂ := b8e561
               grind)
            | exact superpose b8e561 b8e238
            | (have j0 := b8e238 x y
               grind)
            | exact resolve b8e238 b8e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238 b8e561
          have b8e717 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b8e694
          have b8e738 : y = (M.op x y) := by
            first
            | (have r₁ := b8e717
               have r₂ := b8e554
               grind)
            | exact resolve b8e717 b8e554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e554 b8e717
          have b8e816 : y ≠ y ∨ y = (M.op y (M.op x x)) ∨ y = (k y x) := by
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
          have b8e817 : y ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e738
               grind)
            | exact superpose b8e738 b8e16
            | exact resolve b8e16 b8e738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e818 : y = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
          clear b8e816
          have b8e819 : y = (k y x) := by
            first
            | (have r₁ := b8e818
               have r₂ := b8e817
               grind)
            | exact resolve b8e818 b8e817
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e817 b8e818
          have b8e901 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e372 x y
               have i₂ := b8e819
               grind)
            | exact superpose b8e819 b8e372
            | (have j0 := b8e372 x y
               grind)
            | exact resolve b8e372 b8e819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e372 b8e819
          have b8e905 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e901
          have b8e997 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e905
               grind)
            | exact superpose b8e905 b8e20
            | exact resolve b8e20 b8e905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e905
          have b8e1003 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e997
               have i₂ := b8e738
               grind)
            | exact superpose b8e738 b8e997
            | exact resolve b8e997 b8e738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e738 b8e997
          have b8e1004 : False := by grind
          exact b8e1004

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),X) = m(X,m(X,Y)) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxx_pxpxy_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 1))) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) a ≠ M.op a (M.op a b) ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op a (M.op a b))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) a = M.op a (M.op a b) ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op a (M.op a b))).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) a = M.op a (M.op a b) ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op a (M.op a b))).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) x) (M.op x (M.op x y)) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (M.op (σ x) (σ y))) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op y x) x) = (M.op x (M.op x y)) := by grind
      have b0e20 : (M.op (M.op (σ y) (σ x)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e45 : (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op x y) = (k x y) := by
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
      have b0e46 : (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op (M.op y x) x) = (M.op x (M.op x y)) := by grind
        have b1e21 : (M.op (M.op (σ y) (σ x)) (σ x)) ≠ (M.op (σ x) (M.op (σ x) (σ y))) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ y) (σ x)) (σ x)) := by
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
        have b1e25 : (σ y) ≠ (M.op (M.op (σ y) (σ x)) (σ x)) := by
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
        have b1e42 : (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op x y) = (k x y) := by
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
        have b1e43 : (M.op x y) = (k x y) := by grind
        clear b1e42
        have b1e45 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e47 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e45
        have b1e48 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e47
          | exact resolve b1e47 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e48
             have r₂ := b1e25
             grind)
          | exact resolve b1e48 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e48
        have b1e50 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e50
          | exact resolve b1e50 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e50
        have b1e52 : False := by grind
        exact b1e52
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op y x) x) = (M.op x (M.op x y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op x y) = (k x y) := by
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
        have b2e52 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b2e55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
             have i₂ := b2e56 (σ X0) (σ X1)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e315 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
        have b2e325 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e315
             have r₂ := b2e22
             grind)
          | exact resolve b2e315 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e315
        have b2e328 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e325
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e325
          | exact resolve b2e325 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e325
        have b2e329 : False := by grind
        exact b2e329
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (M.op (σ x) (σ y))) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op (M.op y x) x) ≠ (M.op x (M.op x y)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (M.op (σ y) (σ x)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op x y) ≠ (M.op (M.op y x) x) := by
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
        have b3e25 : y ≠ (M.op (M.op y x) x) := by
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
        have b3e42 : (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e45 : (σ y) ≠ (σ (k x y)) := by
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
        have b3e48 : y ≠ y ∨ (M.op x y) = (M.op (M.op y x) x) ∨ y = (k x y) := by
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
        have b3e51 : (M.op x y) = (M.op (M.op y x) x) ∨ y = (k x y) := by grind
        clear b3e48
        have b3e53 : y = (M.op (M.op y x) x) ∨ y = (k x y) := by
          first
          | (have i₁ := b3e51
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e51
          | exact resolve b3e51 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e55 : y = (k x y) := by
          first
          | (have r₁ := b3e53
             have r₂ := b3e25
             grind)
          | exact resolve b3e53 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e53
        have b3e66 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e45
             have i₂ := b3e55
             grind)
          | exact superpose b3e55 b3e45
          | exact resolve b3e45 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e55
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
          have b4e30 : (σ y) ≠ (σ y) := by
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
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op (M.op y x) x) ≠ (M.op x (M.op x y)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op x y) ≠ (M.op (M.op y x) x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27 : y ≠ (M.op (M.op y x) x) := by
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
          have b5e51 : y ≠ y ∨ (M.op x y) = (M.op (M.op y x) x) ∨ y = (k x y) := by
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
          have b5e52 : (M.op x y) = (M.op (M.op y x) x) ∨ y = (k x y) := by grind
          clear b5e51
          have b5e53 : y = (M.op (M.op y x) x) ∨ y = (k x y) := by
            first
            | (have i₁ := b5e52
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e52
            | exact resolve b5e52 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e54 : y = (k x y) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e27
               grind)
            | exact resolve b5e53 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e53
          have b5e59 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e62 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e63 (σ X0) (σ X1)
               grind)
            | exact superpose b5e63 b5e19
            | (have j1 := b5e63 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e369 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e468 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e369 x y
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e369
            | (have j0 := b5e369 x y
               grind)
            | exact resolve b5e369 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e369
          have b5e472 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e468
          have b5e475 : False := by grind
          exact b5e475
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (M.op (σ x) (σ y))) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (M.op (σ y) (σ x)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e53 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b6e56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e72 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e57 x y
             grind)
          | exact superpose b6e57 b6e41
          | (have j1 := b6e57 x y
             grind)
          | exact resolve b6e41 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e57
        have b6e73 : y = (M.op x y) := by grind
        clear b6e72
        have b6e74 : False := by grind
        exact b6e74
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (M.op (σ y) (σ x)) (σ x)) ≠ (M.op (σ x) (M.op (σ x) (σ y))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ y) (σ x)) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : (σ y) ≠ (M.op (M.op (σ y) (σ x)) (σ x)) := by
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
          have b7e64 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e65 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e64
          have b7e66 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e65
            | exact resolve b7e65 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e27
               grind)
            | exact resolve b7e66 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27 b7e66
          have b7e68 : (σ y) = (σ (k x y)) := by
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
          have b7e73 : (k x y) = (τ (σ y)) := by
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
          have b7e74 : y = (k x y) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e73
            | exact resolve b7e73 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e83 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e86 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e86 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e96 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e74
               have i₂ := b7e87 x y
               grind)
            | exact superpose b7e87 b7e74
            | (have j1 := b7e87 x y
               grind)
            | exact resolve b7e74 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e87
          have b7e98 : y = (M.op x y) := by grind
          clear b7e96
          have b7e101 : False := by grind
          exact b7e101
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e72 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e75 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
               have i₂ := b8e76 (σ X0) (σ X1)
               grind)
            | exact superpose b8e76 b8e19
            | (have j1 := b8e76 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e83 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e76 (τ X0) X1
               grind)
            | exact superpose b8e76 b8e25
            | (have j1 := b8e76 (τ X0) X1
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
          have b8e311 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e321 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e311
               have r₂ := b8e24
               grind)
            | exact resolve b8e311 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e311
          have b8e325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e321
               have i₂ := b8e196 x y
               grind)
            | exact superpose b8e196 b8e321
            | (have j1 := b8e196 x y
               grind)
            | (have r₁ := b8e321
               have r₂ := b8e196 x y
               grind)
            | exact resolve b8e321 b8e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e196 b8e321
          have b8e326 : y = (M.op x y) := by grind
          clear b8e325
          have b8e328 : False := by grind
          exact b8e328

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),X) = m(X,m(Y,Y)) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxx_pxpyy_pyx_x_pyx_x_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 0) ⋆ ((Lf 1) ⋆ (Lf 1))) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 0) ⋆ ((Lf 1) ⋆ (Lf 1))) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) a ≠ M.op a (M.op b b) ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op a (M.op b b))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) a = M.op a (M.op b b) ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op a (M.op b b))).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) a = M.op a (M.op b b) ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op a (M.op b b))).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) x) (M.op x (M.op y y)) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (M.op (σ y) (σ y))) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e64 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e64 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e68 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e67 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e85 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e68 (τ X0) X1
           grind)
        | exact superpose b0e68 b0e22
        | (have j1 := b0e68 (τ X0) X1
           grind)
        | exact resolve b0e22 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e68 (σ X0) (σ X1)
           grind)
        | exact superpose b0e68 b0e17
        | (have j1 := b0e68 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e258 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e85 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e85
        | exact resolve b0e85 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85
      have b0e284 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e258 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e258
        | (have j0 := b0e258 X0 X1
           grind)
        | exact resolve b0e258 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e258
      have b0e408 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e87 x y
           grind)
        | exact superpose b0e87 b0e18
        | (have j1 := b0e87 x y
           grind)
        | exact resolve b0e18 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e422 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e87 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e610 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e408
           have i₂ := b0e284 x y
           grind)
        | exact superpose b0e284 b0e408
        | (have j1 := b0e284 (σ x) (σ y)
           grind)
        | (have r₁ := b0e408
           have r₂ := b0e284 x y
           grind)
        | exact resolve b0e408 b0e284
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e408
      have b0e611 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e610
      have b0e614 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e611
           grind)
        | exact superpose b0e611 b0e18
        | exact resolve b0e18 b0e611
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e615 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e611
           grind)
        | exact superpose b0e611 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e611
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e611
           grind)
        | exact resolve b0e15 b0e611
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e616 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e611
           grind)
        | exact superpose b0e611 b0e14
        | exact resolve b0e14 b0e611
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e611
      have b0e617 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
      clear b0e615
      have b0e618 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e616
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e616
        | exact resolve b0e616 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e616
      have b0e619 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e617
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e617
        | exact resolve b0e617 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e617
      have b0e621 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e619
           have r₂ := b0e618
           grind)
        | exact resolve b0e619 b0e618
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e618 b0e619
      have b0e754 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e284 x y
           have i₂ := b0e621
           grind)
        | exact superpose b0e621 b0e284
        | (have j0 := b0e284 x y
           grind)
        | exact resolve b0e284 b0e621
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e284 b0e621
      have b0e777 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e754
      have b0e798 : y = (M.op x y) := by
        first
        | (have r₁ := b0e777
           have r₂ := b0e614
           grind)
        | exact resolve b0e777 b0e614
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e614 b0e777
      have b0e876 : y ≠ y ∨ (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e798
           grind)
        | exact superpose b0e798 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e798
           grind)
        | exact resolve b0e15 b0e798
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e877 : (M.op y y) ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e798
           grind)
        | exact superpose b0e798 b0e14
        | exact resolve b0e14 b0e798
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e878 : (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
      clear b0e876
      have b0e879 : y = (k y x) := by
        first
        | (have r₁ := b0e878
           have r₂ := b0e877
           grind)
        | exact resolve b0e878 b0e877
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e877 b0e878
      have b0e961 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e422 x y
           have i₂ := b0e879
           grind)
        | exact superpose b0e879 b0e422
        | (have j0 := b0e422 x y
           grind)
        | exact resolve b0e422 b0e879
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e422 b0e879
      have b0e965 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e961
      have b0e1057 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e965
           grind)
        | exact superpose b0e965 b0e18
        | exact resolve b0e18 b0e965
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e965
      have b0e1063 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e1057
           have i₂ := b0e798
           grind)
        | exact superpose b0e798 b0e1057
        | exact resolve b0e1057 b0e798
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e798 b0e1057
      have b0e1064 : False := by grind
      exact b0e1064
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b1e56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e59 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e60 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e25 X0 X1
             have i₂ := b1e60 (τ X0) X1
             grind)
          | exact superpose b1e60 b1e25
          | (have j1 := b1e60 (τ X0) X1
             grind)
          | exact resolve b1e25 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e60 (σ X0) (σ X1)
             grind)
          | exact superpose b1e60 b1e18
          | (have j1 := b1e60 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e248 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e71 (σ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e71
          | exact resolve b1e71 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e272 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e248 X0 X1
             have i₂ := b1e18 X1 X0
             grind)
          | exact superpose b1e18 b1e248
          | (have j0 := b1e248 X0 X1
             grind)
          | exact resolve b1e248 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248
        have b1e393 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e72 x y
             grind)
          | exact superpose b1e72 b1e19
          | (have j1 := b1e72 x y
             grind)
          | exact resolve b1e19 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e403 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e72 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e640 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e393
             have i₂ := b1e272 x y
             grind)
          | exact superpose b1e272 b1e393
          | (have j1 := b1e272 (σ x) (σ y)
             grind)
          | (have r₁ := b1e393
             have r₂ := b1e272 x y
             grind)
          | exact resolve b1e393 b1e272
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e393
        have b1e641 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b1e640
        have b1e644 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e641
             grind)
          | exact superpose b1e641 b1e19
          | exact resolve b1e19 b1e641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e645 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e641
             grind)
          | exact superpose b1e641 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e641
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e641
             grind)
          | exact resolve b1e16 b1e641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e646 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e641
             grind)
          | exact superpose b1e641 b1e15
          | exact resolve b1e15 b1e641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e641
        have b1e647 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b1e645
        have b1e648 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e646
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e646
          | exact resolve b1e646 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e646
        have b1e649 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e647
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e647
          | exact resolve b1e647 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e647
        have b1e651 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b1e649
             have r₂ := b1e648
             grind)
          | exact resolve b1e649 b1e648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e648 b1e649
        have b1e786 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e272 x y
             have i₂ := b1e651
             grind)
          | exact superpose b1e651 b1e272
          | (have j0 := b1e272 x y
             grind)
          | exact resolve b1e272 b1e651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e272 b1e651
        have b1e810 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b1e786
        have b1e831 : y = (M.op x y) := by
          first
          | (have r₁ := b1e810
             have r₂ := b1e644
             grind)
          | exact resolve b1e810 b1e644
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e644 b1e810
        have b1e910 : y ≠ y ∨ (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e831
             grind)
          | exact superpose b1e831 b1e16
          | (have j0 := b1e16 y x
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e831
             grind)
          | exact resolve b1e16 b1e831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e911 : (M.op y y) ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e831
             grind)
          | exact superpose b1e831 b1e15
          | exact resolve b1e15 b1e831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e912 : (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
        clear b1e910
        have b1e913 : y = (k y x) := by
          first
          | (have r₁ := b1e912
             have r₂ := b1e911
             grind)
          | exact resolve b1e912 b1e911
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e911 b1e912
        have b1e996 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e403 x y
             have i₂ := b1e913
             grind)
          | exact superpose b1e913 b1e403
          | (have j0 := b1e403 x y
             grind)
          | exact resolve b1e403 b1e913
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e403 b1e913
        have b1e1000 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b1e996
        have b1e1093 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e1000
             grind)
          | exact superpose b1e1000 b1e19
          | exact resolve b1e19 b1e1000
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1000
        have b1e1099 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1093
             have i₂ := b1e831
             grind)
          | exact superpose b1e831 b1e1093
          | exact resolve b1e1093 b1e831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e831 b1e1093
        have b1e1100 : False := by grind
        exact b1e1100
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b2e52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
        have b2e55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e74 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e24 X0 X1
             have i₂ := b2e56 (τ X0) X1
             grind)
          | exact superpose b2e56 b2e24
          | (have j1 := b2e56 (τ X0) X1
             grind)
          | exact resolve b2e24 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e56 (σ X0) (σ X1)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e215 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e74 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e74
          | exact resolve b2e74 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e241 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e215 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e215
          | (have j0 := b2e215 X0 X1
             grind)
          | exact resolve b2e215 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e215
        have b2e366 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
        have b2e376 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e76 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e366
             have i₂ := b2e241 x y
             grind)
          | exact superpose b2e241 b2e366
          | (have j1 := b2e241 (σ x) (σ y)
             grind)
          | (have r₁ := b2e366
             have r₂ := b2e241 x y
             grind)
          | exact resolve b2e366 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e366
        have b2e555 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b2e554
        have b2e558 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e555
             grind)
          | exact superpose b2e555 b2e19
          | exact resolve b2e19 b2e555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e559 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e16 (σ y) (σ x)
             have i₂ := b2e555
             grind)
          | exact superpose b2e555 b2e16
          | (have j0 := b2e16 (σ y) (σ x)
             grind)
          | (have r₁ := b2e16 (σ y) (σ x)
             have r₂ := b2e555
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e555
             grind)
          | exact resolve b2e16 b2e555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e560 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e15 (σ y) (σ x)
             have i₂ := b2e555
             grind)
          | exact superpose b2e555 b2e15
          | exact resolve b2e15 b2e555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e555
        have b2e561 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b2e559
        have b2e562 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e560
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e560
          | exact resolve b2e560 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e560
        have b2e563 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e561
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e561
          | exact resolve b2e561 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e561
        have b2e565 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b2e563
             have r₂ := b2e562
             grind)
          | exact resolve b2e563 b2e562
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e562 b2e563
        have b2e698 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e241 x y
             have i₂ := b2e565
             grind)
          | exact superpose b2e565 b2e241
          | (have j0 := b2e241 x y
             grind)
          | exact resolve b2e241 b2e565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e241 b2e565
        have b2e721 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b2e698
        have b2e742 : y = (M.op x y) := by
          first
          | (have r₁ := b2e721
             have r₂ := b2e558
             grind)
          | exact resolve b2e721 b2e558
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e558 b2e721
        have b2e820 : y ≠ y ∨ (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e742
             grind)
          | exact superpose b2e742 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e742
             grind)
          | exact resolve b2e16 b2e742
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e821 : (M.op y y) ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e742
             grind)
          | exact superpose b2e742 b2e15
          | exact resolve b2e15 b2e742
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e822 : (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
        clear b2e820
        have b2e823 : y = (k y x) := by
          first
          | (have r₁ := b2e822
             have r₂ := b2e821
             grind)
          | exact resolve b2e822 b2e821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e821 b2e822
        have b2e905 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e376 x y
             have i₂ := b2e823
             grind)
          | exact superpose b2e823 b2e376
          | (have j0 := b2e376 x y
             grind)
          | exact resolve b2e376 b2e823
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e376 b2e823
        have b2e909 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e905
        have b2e1001 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e909
             grind)
          | exact superpose b2e909 b2e19
          | exact resolve b2e19 b2e909
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e909
        have b2e1007 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1001
             have i₂ := b2e742
             grind)
          | exact superpose b2e742 b2e1001
          | exact resolve b2e1001 b2e742
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e742 b2e1001
        have b2e1008 : False := by grind
        exact b2e1008
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (M.op (σ y) (σ y))) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b3e62 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e66 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e80 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e25 X0 X1
             have i₂ := b3e66 (τ X0) X1
             grind)
          | exact superpose b3e66 b3e25
          | (have j1 := b3e66 (τ X0) X1
             grind)
          | exact resolve b3e25 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e66 (σ X0) (σ X1)
             grind)
          | exact superpose b3e66 b3e18
          | (have j1 := b3e66 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e291 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e80 (σ X0) X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e80
          | exact resolve b3e80 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e317 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e291 X0 X1
             have i₂ := b3e18 X1 X0
             grind)
          | exact superpose b3e18 b3e291
          | (have j0 := b3e291 X0 X1
             grind)
          | exact resolve b3e291 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e291
        have b3e441 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e82 x y
             grind)
          | exact superpose b3e82 b3e19
          | (have j1 := b3e82 x y
             grind)
          | exact resolve b3e19 b3e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e454 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e82 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e647 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e441
             have i₂ := b3e317 x y
             grind)
          | exact superpose b3e317 b3e441
          | (have j1 := b3e317 (σ x) (σ y)
             grind)
          | (have r₁ := b3e441
             have r₂ := b3e317 x y
             grind)
          | exact resolve b3e441 b3e317
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e441
        have b3e648 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b3e647
        have b3e724 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e648
             grind)
          | exact superpose b3e648 b3e19
          | exact resolve b3e19 b3e648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e725 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e648
             grind)
          | exact superpose b3e648 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | (have r₁ := b3e16 (σ y) (σ x)
             have r₂ := b3e648
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e648
             grind)
          | exact resolve b3e16 b3e648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e726 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e648
             grind)
          | exact superpose b3e648 b3e15
          | exact resolve b3e15 b3e648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e648
        have b3e727 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b3e725
        have b3e728 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e726
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e726
          | exact resolve b3e726 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e726
        have b3e729 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e727
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e727
          | exact resolve b3e727 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e727
        have b3e731 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b3e729
             have r₂ := b3e728
             grind)
          | exact resolve b3e729 b3e728
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e728 b3e729
        have b3e876 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e317 x y
             have i₂ := b3e731
             grind)
          | exact superpose b3e731 b3e317
          | (have j0 := b3e317 x y
             grind)
          | exact resolve b3e317 b3e731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e317 b3e731
        have b3e899 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b3e876
        have b3e920 : y = (M.op x y) := by
          first
          | (have r₁ := b3e899
             have r₂ := b3e724
             grind)
          | exact resolve b3e899 b3e724
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e724 b3e899
        have b3e1002 : y ≠ y ∨ (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e920
             grind)
          | exact superpose b3e920 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e920
             grind)
          | exact resolve b3e16 b3e920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1003 : (M.op y y) ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e920
             grind)
          | exact superpose b3e920 b3e15
          | exact resolve b3e15 b3e920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1004 : (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
        clear b3e1002
        have b3e1005 : y = (k y x) := by
          first
          | (have r₁ := b3e1004
             have r₂ := b3e1003
             grind)
          | exact resolve b3e1004 b3e1003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1003 b3e1004
        have b3e1097 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e454 x y
             have i₂ := b3e1005
             grind)
          | exact superpose b3e1005 b3e454
          | (have j0 := b3e454 x y
             grind)
          | exact resolve b3e454 b3e1005
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e454 b3e1005
        have b3e1101 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b3e1097
        have b3e1197 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1101
             grind)
          | exact superpose b3e1101 b3e19
          | exact resolve b3e19 b3e1101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1101
        have b3e1203 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e1197
             have i₂ := b3e920
             grind)
          | exact superpose b3e920 b3e1197
          | exact resolve b3e1197 b3e920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e920 b3e1197
        have b3e1204 : False := by grind
        exact b3e1204
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b4e53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
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
          have b4e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e222 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e70 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e70
            | exact resolve b4e70 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e248 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e222 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e222
            | (have j0 := b4e222 X0 X1
               grind)
            | exact resolve b4e222 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e222
          have b4e374 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e72 x y
               grind)
            | exact superpose b4e72 b4e20
            | (have j1 := b4e72 x y
               grind)
            | exact resolve b4e20 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e384 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e560 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e374
               have i₂ := b4e248 x y
               grind)
            | exact superpose b4e248 b4e374
            | (have j1 := b4e248 (σ x) (σ y)
               grind)
            | (have r₁ := b4e374
               have r₂ := b4e248 x y
               grind)
            | exact resolve b4e374 b4e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e374
          have b4e561 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b4e560
          have b4e564 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e561
               grind)
            | exact superpose b4e561 b4e20
            | exact resolve b4e20 b4e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e565 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e561
               grind)
            | exact superpose b4e561 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e561
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e561
               grind)
            | exact resolve b4e17 b4e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e566 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e561
               grind)
            | exact superpose b4e561 b4e16
            | exact resolve b4e16 b4e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e561
          have b4e567 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b4e565
          have b4e568 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e566
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e566
            | exact resolve b4e566 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e566
          have b4e569 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e567
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e567
            | exact resolve b4e567 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e567
          have b4e571 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e569
               have r₂ := b4e568
               grind)
            | exact resolve b4e569 b4e568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e568 b4e569
          have b4e704 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e248 x y
               have i₂ := b4e571
               grind)
            | exact superpose b4e571 b4e248
            | (have j0 := b4e248 x y
               grind)
            | exact resolve b4e248 b4e571
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e248 b4e571
          have b4e727 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b4e704
          have b4e748 : y = (M.op x y) := by
            first
            | (have r₁ := b4e727
               have r₂ := b4e564
               grind)
            | exact resolve b4e727 b4e564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e564 b4e727
          have b4e826 : y ≠ y ∨ (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e748
               grind)
            | exact superpose b4e748 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e748
               grind)
            | exact resolve b4e17 b4e748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e827 : (M.op y y) ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e748
               grind)
            | exact superpose b4e748 b4e16
            | exact resolve b4e16 b4e748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e828 : (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
          clear b4e826
          have b4e829 : y = (k y x) := by
            first
            | (have r₁ := b4e828
               have r₂ := b4e827
               grind)
            | exact resolve b4e828 b4e827
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e827 b4e828
          have b4e911 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e384 x y
               have i₂ := b4e829
               grind)
            | exact superpose b4e829 b4e384
            | (have j0 := b4e384 x y
               grind)
            | exact resolve b4e384 b4e829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e384 b4e829
          have b4e915 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b4e911
          have b4e1007 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e915
               grind)
            | exact superpose b4e915 b4e20
            | exact resolve b4e20 b4e915
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e915
          have b4e1013 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e1007
               have i₂ := b4e748
               grind)
            | exact superpose b4e748 b4e1007
            | exact resolve b4e1007 b4e748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e748 b4e1007
          have b4e1014 : False := by grind
          exact b4e1014
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op (M.op y x) x) ≠ (M.op x (M.op y y)) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op x (M.op y y)) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : x ≠ x ∨ (M.op x (M.op y y)) = (M.op x x) ∨ x = (k x y) := by
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
          have b5e42 : (M.op x (M.op y y)) = (M.op x x) ∨ x = (k x y) := by grind
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
          have b5e48 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
          have b5e51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e48 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e381 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e69 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e482 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e381 y x
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e381
            | (have j0 := b5e381 y x
               grind)
            | exact resolve b5e381 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e381
          have b5e486 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e482
          have b5e489 : False := by grind
          exact b5e489
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (M.op (σ y) (σ y))) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e61 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
        have b6e64 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e65 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e65 (σ X0) (σ X1)
             grind)
          | exact superpose b6e65 b6e18
          | (have j1 := b6e65 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e86 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X0 X1
             have i₂ := b6e65 (τ X0) X1
             grind)
          | exact superpose b6e65 b6e24
          | (have j1 := b6e65 (τ X0) X1
             grind)
          | exact resolve b6e24 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e65
        have b6e249 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e86 (σ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e86
          | exact resolve b6e86 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e275 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e249 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e249
          | (have j0 := b6e249 X0 X1
             grind)
          | exact resolve b6e249 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e249
        have b6e398 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e83 x y
             grind)
          | exact superpose b6e83 b6e19
          | (have j1 := b6e83 x y
             grind)
          | exact resolve b6e19 b6e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e410 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e83 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e592 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e398
             have i₂ := b6e275 x y
             grind)
          | exact superpose b6e275 b6e398
          | (have j1 := b6e275 (σ x) (σ y)
             grind)
          | (have r₁ := b6e398
             have r₂ := b6e275 x y
             grind)
          | exact resolve b6e398 b6e275
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e398
        have b6e593 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b6e592
        have b6e596 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e593
             grind)
          | exact superpose b6e593 b6e19
          | exact resolve b6e19 b6e593
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e597 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e593
             grind)
          | exact superpose b6e593 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e593
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e593
             grind)
          | exact resolve b6e16 b6e593
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e598 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e593
             grind)
          | exact superpose b6e593 b6e15
          | exact resolve b6e15 b6e593
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e593
        have b6e599 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b6e597
        have b6e600 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e598
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e598
          | exact resolve b6e598 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e598
        have b6e601 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e599
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e599
          | exact resolve b6e599 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e599
        have b6e603 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e601
             have r₂ := b6e600
             grind)
          | exact resolve b6e601 b6e600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e600 b6e601
        have b6e736 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e275 x y
             have i₂ := b6e603
             grind)
          | exact superpose b6e603 b6e275
          | (have j0 := b6e275 x y
             grind)
          | exact resolve b6e275 b6e603
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e275 b6e603
        have b6e759 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b6e736
        have b6e780 : y = (M.op x y) := by
          first
          | (have r₁ := b6e759
             have r₂ := b6e596
             grind)
          | exact resolve b6e759 b6e596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e596 b6e759
        have b6e858 : y ≠ y ∨ (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e780
             grind)
          | exact superpose b6e780 b6e16
          | (have j0 := b6e16 y x
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e780
             grind)
          | exact resolve b6e16 b6e780
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e859 : (M.op y y) ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e780
             grind)
          | exact superpose b6e780 b6e15
          | exact resolve b6e15 b6e780
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e860 : (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
        clear b6e858
        have b6e861 : y = (k y x) := by
          first
          | (have r₁ := b6e860
             have r₂ := b6e859
             grind)
          | exact resolve b6e860 b6e859
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e859 b6e860
        have b6e943 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e410 x y
             have i₂ := b6e861
             grind)
          | exact superpose b6e861 b6e410
          | (have j0 := b6e410 x y
             grind)
          | exact resolve b6e410 b6e861
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e410 b6e861
        have b6e947 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b6e943
        have b6e1039 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e947
             grind)
          | exact superpose b6e947 b6e19
          | exact resolve b6e19 b6e947
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e947
        have b6e1045 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b6e1039
             have i₂ := b6e780
             grind)
          | exact superpose b6e780 b6e1039
          | exact resolve b6e1039 b6e780
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e780 b6e1039
        have b6e1046 : False := by grind
        exact b6e1046
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (M.op (M.op (σ y) (σ x)) (σ x)) ≠ (M.op (σ x) (M.op (σ y) (σ y))) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ x) (M.op (σ y) (σ y))) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e62 : (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
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
          have b7e79 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          have b7e82 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e79 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e83 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e82 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e95 : x = (M.op y x) ∨ x = (M.op y x) := by
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
          have b7e97 : x = (M.op y x) := by grind
          clear b7e95
          have b7e100 : False := by grind
          exact b7e100
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e74 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          have b8e77 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e74 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e78 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e90 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
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
          have b8e184 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e90 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e90
            | exact resolve b8e90 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e208 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e184 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e184
            | (have j0 := b8e184 X0 X1
               grind)
            | exact resolve b8e184 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e325 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e335 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e86 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e593 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e325
               have i₂ := b8e208 x y
               grind)
            | exact superpose b8e208 b8e325
            | (have j1 := b8e208 (σ x) (σ y)
               grind)
            | (have r₁ := b8e325
               have r₂ := b8e208 x y
               grind)
            | exact resolve b8e325 b8e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e325
          have b8e594 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b8e593
          have b8e597 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e594
               grind)
            | exact superpose b8e594 b8e20
            | exact resolve b8e20 b8e594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e598 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e594
               grind)
            | exact superpose b8e594 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e594
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e594
               grind)
            | exact resolve b8e17 b8e594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e599 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e594
               grind)
            | exact superpose b8e594 b8e16
            | exact resolve b8e16 b8e594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e594
          have b8e600 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e598
          have b8e601 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e599
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e599
            | exact resolve b8e599 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e599
          have b8e602 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e600
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e600
            | exact resolve b8e600 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e600
          have b8e604 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e602
               have r₂ := b8e601
               grind)
            | exact resolve b8e602 b8e601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e601 b8e602
          have b8e747 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e208 x y
               have i₂ := b8e604
               grind)
            | exact superpose b8e604 b8e208
            | (have j0 := b8e208 x y
               grind)
            | exact resolve b8e208 b8e604
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208 b8e604
          have b8e771 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b8e747
          have b8e792 : y = (M.op x y) := by
            first
            | (have r₁ := b8e771
               have r₂ := b8e597
               grind)
            | exact resolve b8e771 b8e597
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e597 b8e771
          have b8e875 : y ≠ y ∨ (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e792
               grind)
            | exact superpose b8e792 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e792
               grind)
            | exact resolve b8e17 b8e792
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e876 : (M.op y y) ≠ (M.op y (M.op x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e792
               grind)
            | exact superpose b8e792 b8e16
            | exact resolve b8e16 b8e792
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e877 : (M.op y y) = (M.op y (M.op x x)) ∨ y = (k y x) := by grind
          clear b8e875
          have b8e878 : y = (k y x) := by
            first
            | (have r₁ := b8e877
               have r₂ := b8e876
               grind)
            | exact resolve b8e877 b8e876
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e876 b8e877
          have b8e966 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e335 x y
               have i₂ := b8e878
               grind)
            | exact superpose b8e878 b8e335
            | (have j0 := b8e335 x y
               grind)
            | exact resolve b8e335 b8e878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e335 b8e878
          have b8e970 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e966
          have b8e1067 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e970
               grind)
            | exact superpose b8e970 b8e20
            | exact resolve b8e20 b8e970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e970
          have b8e1073 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e1067
               have i₂ := b8e792
               grind)
            | exact superpose b8e792 b8e1067
            | exact resolve b8e1067 b8e792
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e792 b8e1067
          have b8e1074 : False := by grind
          exact b8e1074
