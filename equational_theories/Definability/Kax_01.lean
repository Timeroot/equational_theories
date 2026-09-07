import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1271`: `x = x ◇ (((y ◇ z) ◇ w) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pxy_pyx_Equation1271 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1271 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1271.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
           have i₂ := b0e11 (M.op X0 X1) x x x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e30 X0 (M.op (M.op x x) x) X1
           have i₂ := b0e30 x x X0
           grind)
        | exact superpose b0e30 b0e30
        | exact resolve b0e30 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e68 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e35 y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e69 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e35 (σ y) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e35
        | exact resolve b0e35 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e170 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e69 (σ x)
           grind)
        | exact superpose b0e69 b0e18
        | exact resolve b0e18 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e173 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e170
           have i₂ := b0e68 x
           grind)
        | exact superpose b0e68 b0e170
        | exact resolve b0e170 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68 b0e170
      have b0e174 : False := by grind
      exact b0e174
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e39 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e39 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e56 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e46 (σ y)
             grind)
          | exact superpose b1e46 b1e21
          | exact resolve b1e21 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e112 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) y) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e104 X0 X1
             have i₂ := b1e46 (σ X0)
             grind)
          | exact superpose b1e46 b1e104
          | (have j0 := b1e104 X0 X1
             grind)
          | exact resolve b1e104 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104
        have b1e114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) y) ∨ (σ X1) = (k (σ X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e112 X0 X1
             have i₂ := b1e46 (σ X1)
             grind)
          | exact superpose b1e46 b1e112
          | (have j0 := b1e112 X0 X1
             grind)
          | exact resolve b1e112 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112
        have b1e1511 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e114 y y
             grind)
          | exact superpose b1e114 b1e21
          | (have j1 := b1e114 y y
             grind)
          | exact resolve b1e21 b1e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114
        have b1e1564 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b1e1511
        have b1e1597 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e1564
             have r₂ := b1e56
             grind)
          | exact resolve b1e1564 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e1564
        have b1e1621 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e1597
             have i₂ := b1e46 y
             grind)
          | exact superpose b1e46 b1e1597
          | exact resolve b1e1597 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e1597
        have b1e1629 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1621
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1621
          | exact resolve b1e1621 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1621
        have b1e1630 : False := by grind
        exact b1e1630
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b2e37 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e51 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e42 (σ y)
             grind)
          | exact superpose b2e42 b2e21
          | exact resolve b2e21 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e94 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X0 X2
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e102 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e94 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e108 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) y) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e98 X0 X1
             have i₂ := b2e42 (σ X0)
             grind)
          | exact superpose b2e42 b2e98
          | (have j0 := b2e98 X0 X1
             grind)
          | exact resolve b2e98 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e110 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) y) ∨ (σ X1) = (k (σ X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e108 X0 X1
             have i₂ := b2e42 (σ X1)
             grind)
          | exact superpose b2e42 b2e108
          | (have j0 := b2e108 X0 X1
             grind)
          | exact resolve b2e108 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108
        have b2e693 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e102 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e102
        have b2e694 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e693 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e693
        have b2e702 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e694 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e694 x
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e694 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e694
        have b2e720 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e23 X0 (τ X0)
             have i₂ := b2e702 (τ X0)
             grind)
          | exact superpose b2e702 b2e23
          | exact resolve b2e23 b2e702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e721 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e720 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e720
          | exact resolve b2e720 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e720
        have b2e725 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b2e721 X0
             have i₂ := b2e42 (τ X0)
             grind)
          | exact superpose b2e42 b2e721
          | exact resolve b2e721 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e721
        have b2e729 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e725 X0
             have i₂ := b2e23 X0 y
             grind)
          | exact superpose b2e23 b2e725
          | exact resolve b2e725 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e725
        have b2e909 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e729 (σ X0)
             grind)
          | (have i₁ := b2e18 X0 y
             have i₂ := b2e729 (σ X0)
             grind)
          | exact superpose b2e729 b2e18
          | exact resolve b2e18 b2e729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e729
        have b2e916 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e909 X0
             have i₂ := b2e702 X0
             grind)
          | exact superpose b2e702 b2e909
          | exact resolve b2e909 b2e702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e702 b2e909
        have b2e934 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e916 X0
             have i₂ := b2e18 X0 y
             grind)
          | exact superpose b2e18 b2e916
          | exact resolve b2e916 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e916
        have b2e1604 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e110 y y
             grind)
          | exact superpose b2e110 b2e21
          | (have j1 := b2e110 y y
             grind)
          | exact resolve b2e21 b2e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e110
        have b2e1661 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b2e1604
        have b2e1698 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b2e1661
             have r₂ := b2e51
             grind)
          | exact resolve b2e1661 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e1661
        have b2e1726 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1698
             have i₂ := b2e934 y
             grind)
          | exact superpose b2e934 b2e1698
          | exact resolve b2e1698 b2e934
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e934 b2e1698
        have b2e1734 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1726
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1726
          | exact resolve b2e1726 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1726
        have b2e1735 : False := by grind
        exact b2e1735
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
        have b3e39 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 X0 x
             grind)
          | (have r₁ := b3e15 X0 x
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b3e39 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e56 : (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e46 (σ y)
             grind)
          | exact superpose b3e46 b3e22
          | exact resolve b3e22 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e99 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X1 X0
             have i₂ := b3e17 X0 X2
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X1 X0
             have j1 := b3e17 X2 X2
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e103 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e99 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e141 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e45 (σ X0)
             grind)
          | exact superpose b3e45 b3e18
          | exact resolve b3e18 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e143 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e141 X0
             have i₂ := b3e46 (σ X0)
             grind)
          | exact superpose b3e46 b3e141
          | exact resolve b3e141 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141
        have b3e620 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e103 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e621 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e620 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e620
        have b3e629 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e621 X0
             have j1 := b3e15 X0 X0
             grind)
          | (have r₁ := b3e621 x
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e621 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e621
        have b3e656 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e23 X0 (τ X0)
             have i₂ := b3e629 (τ X0)
             grind)
          | exact superpose b3e629 b3e23
          | exact resolve b3e23 b3e629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e657 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e656 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e656
          | exact resolve b3e656 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e656
        have b3e661 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) x)) := by
          intro X0
          first
          | (have i₁ := b3e657 X0
             have i₂ := b3e46 (τ X0)
             grind)
          | exact superpose b3e46 b3e657
          | exact resolve b3e657 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e657
        have b3e665 : ∀ X0 : G, (k X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e661 X0
             have i₂ := b3e23 X0 x
             grind)
          | exact superpose b3e23 b3e661
          | exact resolve b3e661 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e661
        have b3e817 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e629 X0
             have i₂ := b3e665 X0
             grind)
          | (have i₁ := b3e629 (σ x)
             have i₂ := b3e665 (σ x)
             grind)
          | exact superpose b3e665 b3e629
          | exact resolve b3e629 b3e665
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1014 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e46 X0
             have i₂ := b3e817 X0
             grind)
          | exact superpose b3e817 b3e46
          | exact resolve b3e46 b3e817
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1044 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 x
             have i₂ := b3e817 (σ X0)
             grind)
          | exact superpose b3e817 b3e18
          | exact resolve b3e18 b3e817
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e817
        have b3e1049 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e1044 X0
             have i₂ := b3e46 (σ X0)
             grind)
          | exact superpose b3e46 b3e1044
          | exact resolve b3e1044 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e1044
        have b3e1070 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e1049 X0
             have i₂ := b3e143 X0
             grind)
          | exact superpose b3e143 b3e1049
          | exact resolve b3e1049 b3e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1049
        have b3e1280 : ∀ X0 : G, (k X0 x) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e665 X0
             have i₂ := b3e1014 X0
             grind)
          | exact superpose b3e1014 b3e665
          | exact resolve b3e665 b3e1014
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e665 b3e1014
        have b3e1571 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e23 X0 (τ X0)
             have i₂ := b3e1280 (τ X0)
             grind)
          | (have i₁ := b3e23 X0 x
             have i₂ := b3e1280 (τ X0)
             grind)
          | exact superpose b3e1280 b3e23
          | exact resolve b3e23 b3e1280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1280
        have b3e1574 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) x)) := by
          intro X0
          first
          | (have i₁ := b3e1571 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1571
          | exact resolve b3e1571 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1571
        have b3e1579 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b3e1574 X0
             have i₂ := b3e1070 (τ X0)
             grind)
          | exact superpose b3e1070 b3e1574
          | exact resolve b3e1574 b3e1070
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1070 b3e1574
        have b3e1581 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e1579 X0
             have i₂ := b3e23 X0 y
             grind)
          | exact superpose b3e23 b3e1579
          | exact resolve b3e1579 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e1579
        have b3e1786 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e1581 (σ X0)
             grind)
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e1581 (σ X0)
             grind)
          | exact superpose b3e1581 b3e18
          | exact resolve b3e18 b3e1581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1581
        have b3e1791 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e1786 X0
             have i₂ := b3e629 X0
             grind)
          | exact superpose b3e629 b3e1786
          | exact resolve b3e1786 b3e629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e629 b3e1786
        have b3e1799 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e1791 X0
             have i₂ := b3e18 X0 y
             grind)
          | exact superpose b3e18 b3e1791
          | exact resolve b3e1791 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1791
        have b3e1881 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e143 y
             grind)
          | exact superpose b3e143 b3e56
          | exact resolve b3e56 b3e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e143
        have b3e1889 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e1881
             have i₂ := b3e1799 y
             grind)
          | exact superpose b3e1799 b3e1881
          | exact resolve b3e1881 b3e1799
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1799 b3e1881
        have b3e1998 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (M.op y y)
             have i₂ := b3e1889
             grind)
          | exact superpose b3e1889 b3e13
          | exact resolve b3e13 b3e1889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1889
        have b3e1999 : y = (M.op y y) := by
          first
          | (have i₁ := b3e1998
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1998
          | exact resolve b3e1998 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1998
        have b3e2003 : False := by grind
        exact b3e2003
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
            intro X0 X1 X2 X3
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
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
          have b4e34 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
               have i₂ := b4e13 (M.op X0 X1) x x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X0 (M.op (M.op x x) x) X1
               have i₂ := b4e34 x x X0
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e45 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 X0 x
               grind)
            | (have r₁ := b4e16 X0 x
               have r₂ := b4e22
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 X0 (σ x)
               grind)
            | (have r₁ := b4e16 X0 (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e45 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e62 : (σ y) ≠ (k (σ y) x) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e52 (σ y)
               grind)
            | exact superpose b4e52 b4e23
            | exact resolve b4e23 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e65 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65
          have b4e72 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e64 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e107 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X2 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e114 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e107 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e107
          have b4e154 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e51 (σ X0)
               grind)
            | exact superpose b4e51 b4e19
            | exact resolve b4e19 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e158 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e154 X0
               have i₂ := b4e52 (σ X0)
               grind)
            | exact superpose b4e52 b4e154
            | exact resolve b4e154 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e154
          have b4e194 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e72 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e72 X0
               grind)
            | exact resolve b4e16 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e196 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e39
            | (have j1 := b4e72 X0
               grind)
            | exact resolve b4e39 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e72
          have b4e207 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have j0 := b4e194 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194
          have b4e327 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e71 (σ X0)
               grind)
            | exact superpose b4e71 b4e19
            | (have j1 := b4e71 (σ X0)
               grind)
            | exact resolve b4e19 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e337 : ∀ X0 : G, (σ X0) = (k (σ X0) x) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e327 X0
               have i₂ := b4e52 (σ X0)
               grind)
            | exact superpose b4e52 b4e327
            | (have j0 := b4e327 X0
               grind)
            | exact resolve b4e327 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e327
          have b4e343 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e337 X0
               have i₂ := b4e158 X0
               grind)
            | exact superpose b4e158 b4e337
            | (have j0 := b4e337 X0
               grind)
            | exact resolve b4e337 b4e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e337
          have b4e768 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e114 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114
          have b4e769 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e768 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e768
          have b4e778 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e769 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e769 x
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e769 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e769
          have b4e807 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e25 X0 (τ X0)
               have i₂ := b4e778 (τ X0)
               grind)
            | exact superpose b4e778 b4e25
            | exact resolve b4e25 b4e778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e808 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e807 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e807
            | exact resolve b4e807 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e807
          have b4e812 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e808 X0
               have i₂ := b4e52 (τ X0)
               grind)
            | exact superpose b4e52 b4e808
            | exact resolve b4e808 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52 b4e808
          have b4e816 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e812 X0
               have i₂ := b4e25 X0 x
               grind)
            | exact superpose b4e25 b4e812
            | exact resolve b4e812 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e812
          have b4e1003 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e816 (σ X0)
               grind)
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e816 (σ X0)
               grind)
            | exact superpose b4e816 b4e19
            | exact resolve b4e19 b4e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e816
          have b4e1009 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1003 X0
               have i₂ := b4e778 X0
               grind)
            | exact superpose b4e778 b4e1003
            | exact resolve b4e1003 b4e778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e778 b4e1003
          have b4e1015 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1009 X0
               have i₂ := b4e19 X0 x
               grind)
            | exact superpose b4e19 b4e1009
            | exact resolve b4e1009 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1009
          have b4e1376 : (σ y) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b4e62
               have i₂ := b4e158 y
               grind)
            | exact superpose b4e158 b4e62
            | exact resolve b4e62 b4e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62 b4e158
          have b4e1386 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e1376
               have i₂ := b4e1015 y
               grind)
            | exact superpose b4e1015 b4e1376
            | exact resolve b4e1376 b4e1015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1376
          have b4e7242 : ∀ X0 : G, (M.op x x) ≠ (M.op x X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e207 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e207
          have b4e7247 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e7242 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e7242
            | (have j0 := b4e7242 X0
               grind)
            | exact resolve b4e7242 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7242
          have b4e7284 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e7247 X0
               have j1 := b4e196 X0 x
               grind)
            | (have r₁ := b4e7247 X0
               have r₂ := b4e196 X0 x
               grind)
            | exact resolve b4e7247 b4e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e196 b4e7247
          have b4e19855 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e343 y
               grind)
            | exact superpose b4e343 b4e20
            | (have j1 := b4e343 y
               grind)
            | exact resolve b4e20 b4e343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e343
          have b4e20001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b4e19855
               have i₂ := b4e7284 y
               grind)
            | exact superpose b4e7284 b4e19855
            | exact resolve b4e19855 b4e7284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7284 b4e19855
          have b4e20002 : (σ y) = (σ (k y x)) := by grind
          clear b4e20001
          have b4e20060 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20002
               have i₂ := b4e1015 y
               grind)
            | exact superpose b4e1015 b4e20002
            | exact resolve b4e20002 b4e1015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1015 b4e20002
          have b4e20072 : False := by grind
          exact b4e20072
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e43 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b5e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e58 : (σ x) ≠ (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e48 (σ x)
               grind)
            | exact superpose b5e48 b5e24
            | exact resolve b5e24 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e100 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X0 X2
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e109 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e100 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100
          have b5e116 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) x) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e104 X0 X1
               have i₂ := b5e48 (σ X0)
               grind)
            | exact superpose b5e48 b5e104
            | (have j0 := b5e104 X0 X1
               grind)
            | exact resolve b5e104 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104
          have b5e118 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) x) ∨ (σ X1) = (k (σ X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e116 X0 X1
               have i₂ := b5e48 (σ X1)
               grind)
            | exact superpose b5e48 b5e116
            | (have j0 := b5e116 X0 X1
               grind)
            | exact resolve b5e116 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116
          have b5e625 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e109 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e109
          have b5e626 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e625 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e625
          have b5e634 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e626 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e626 x
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e626 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e626
          have b5e652 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e25 X0 (τ X0)
               have i₂ := b5e634 (τ X0)
               grind)
            | exact superpose b5e634 b5e25
            | exact resolve b5e25 b5e634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e653 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e652 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e652
            | exact resolve b5e652 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e652
          have b5e657 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e653 X0
               have i₂ := b5e48 (τ X0)
               grind)
            | exact superpose b5e48 b5e653
            | exact resolve b5e653 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e653
          have b5e661 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e657 X0
               have i₂ := b5e25 X0 x
               grind)
            | exact superpose b5e25 b5e657
            | exact resolve b5e657 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e657
          have b5e835 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e661 (σ X0)
               grind)
            | (have i₁ := b5e19 X0 x
               have i₂ := b5e661 (σ X0)
               grind)
            | exact superpose b5e661 b5e19
            | exact resolve b5e19 b5e661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e661
          have b5e842 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e835 X0
               have i₂ := b5e634 X0
               grind)
            | exact superpose b5e634 b5e835
            | exact resolve b5e835 b5e634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e634 b5e835
          have b5e860 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e842 X0
               have i₂ := b5e19 X0 x
               grind)
            | exact superpose b5e19 b5e842
            | exact resolve b5e842 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e842
          have b5e1514 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) x) ∨ (σ x) = (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e118 x x
               grind)
            | exact superpose b5e118 b5e24
            | (have j1 := b5e118 x x
               grind)
            | exact resolve b5e24 b5e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118
          have b5e1567 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) x) := by grind
          clear b5e1514
          have b5e1603 : (σ x) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b5e1567
               have r₂ := b5e58
               grind)
            | exact resolve b5e1567 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58 b5e1567
          have b5e1630 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1603
               have i₂ := b5e860 x
               grind)
            | exact superpose b5e860 b5e1603
            | exact resolve b5e1603 b5e860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e860 b5e1603
          have b5e1639 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e1630
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1630
            | exact resolve b5e1630 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1630
          have b5e1640 : False := by grind
          exact b5e1640
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
             have i₂ := b6e12 (M.op X0 X1) x x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e27 X0 (M.op (M.op x x) x) X1
             have i₂ := b6e27 x x X0
             grind)
          | exact superpose b6e27 b6e27
          | exact resolve b6e27 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e37 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e43 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e31
          | exact resolve b6e31 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e82 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X0 X2
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 X2 X2
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e87 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e82 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e42 (σ X0)
             grind)
          | exact superpose b6e42 b6e18
          | exact resolve b6e18 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e631 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e87 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e632 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e631 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e631
        have b6e638 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e632 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e632 x
             have r₂ := b6e15 X0 x
             grind)
          | exact resolve b6e632 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e632
        have b6e1453 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e43 (σ y)
             have i₂ := b6e109 y
             grind)
          | exact superpose b6e109 b6e43
          | exact resolve b6e43 b6e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e109
        have b6e1487 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e1453
             have i₂ := b6e638 y
             grind)
          | exact superpose b6e638 b6e1453
          | exact resolve b6e1453 b6e638
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e638 b6e1453
        have b6e1792 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e1487
             grind)
          | exact superpose b6e1487 b6e13
          | exact resolve b6e13 b6e1487
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1487
        have b6e1803 : y = (M.op y y) := by
          first
          | (have i₁ := b6e1792
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1792
          | exact resolve b6e1792 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1792
        have b6e1805 : False := by grind
        exact b6e1805
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e25 X0 X1
               grind)
            | exact superpose b7e25 b7e14
            | exact resolve b7e14 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25
          have b7e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b7e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e88 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 X1 X0
               have i₂ := b7e18 X0 X2
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X0
               have j1 := b7e18 X2 X2
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e96 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e88 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 x
               have i₂ := b7e48 (σ X0)
               grind)
            | exact superpose b7e48 b7e19
            | exact resolve b7e19 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e721 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e96 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e722 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e721 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e721
          have b7e729 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e722 X0
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e722 x
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e722 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e722
          have b7e1538 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
            intro X0
            first
            | (have i₁ := b7e30 (σ X0) X0
               have i₂ := b7e729 (σ X0)
               grind)
            | exact superpose b7e729 b7e30
            | exact resolve b7e30 b7e729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e1558 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (σ (k X0 x))) := by
            intro X0
            first
            | (have i₁ := b7e1538 X0
               have i₂ := b7e119 X0
               grind)
            | exact superpose b7e119 b7e1538
            | exact resolve b7e1538 b7e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119 b7e1538
          have b7e1562 : ∀ X0 : G, (k X0 x) = (k (τ (σ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b7e1558 X0
               have i₂ := b7e14 (k X0 x)
               grind)
            | exact superpose b7e14 b7e1558
            | exact resolve b7e1558 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1558
          have b7e1565 : ∀ X0 : G, (k X0 x) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b7e1562 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e1562
            | exact resolve b7e1562 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1562
          have b7e1985 : (M.op (σ x) (σ x)) = (k (σ x) x) := by
            first
            | (have i₁ := b7e48 (σ x)
               have i₂ := b7e1565 (σ x)
               grind)
            | exact superpose b7e1565 b7e48
            | exact resolve b7e48 b7e1565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e1989 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e1565 (σ X0)
               grind)
            | exact superpose b7e1565 b7e19
            | exact resolve b7e19 b7e1565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1565
          have b7e1997 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b7e1989 X0
               have i₂ := b7e729 X0
               grind)
            | exact superpose b7e729 b7e1989
            | exact resolve b7e1989 b7e729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e729 b7e1989
          have b7e2000 : (σ x) = (k (σ x) x) := by
            first
            | (have i₁ := b7e1985
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1985
            | exact resolve b7e1985 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1985
          have b7e2026 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e2000
               have i₂ := b7e1997 x
               grind)
            | exact superpose b7e1997 b7e2000
            | exact resolve b7e2000 b7e1997
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1997 b7e2000
          have b7e2333 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e2026
               grind)
            | exact superpose b7e2026 b7e14
            | exact resolve b7e14 b7e2026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2026
          have b7e2348 : x = (M.op x x) := by
            first
            | (have i₁ := b7e2333
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2333
            | exact resolve b7e2333 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2333
          have b7e2351 : False := by grind
          exact b7e2351
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e98 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) X0
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) x
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e103 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e98 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98
          have b8e293 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e103 (σ X0)
               grind)
            | exact superpose b8e103 b8e19
            | (have j1 := b8e103 (σ X0)
               grind)
            | exact resolve b8e19 b8e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e8607 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e293 x
               grind)
            | exact superpose b8e293 b8e20
            | (have j1 := b8e293 x
               grind)
            | exact resolve b8e20 b8e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293
          have b8e8780 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e8607
               have r₂ := b8e24
               grind)
            | exact resolve b8e8607 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8607
          have b8e8826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e8780
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e8780
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e8780 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8780
          have b8e8839 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e8826
          have b8e8846 : y = (M.op y y) := by
            first
            | (have r₁ := b8e8839
               have r₂ := b8e22
               grind)
            | exact resolve b8e8839 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8839
          have b8e8847 : False := by grind
          exact b8e8847

/-- `Equation1636`: `x = (x ◇ x) ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pxy_pxy_x_pxy_Equation1636 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1636 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1636.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e36 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e37 : (M.op x y) = (k x y) := by grind
      have b0e39 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e36
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e36
        | exact resolve b0e36 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e40 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e39
        | exact resolve b0e39 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e39
      have b0e41 : False := by grind
      exact b0e41
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k (τ X0) X1)
             have i₂ := b1e25 X0 X1
             grind)
          | exact superpose b1e25 b1e13
          | exact resolve b1e13 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 : G, x = (M.op y (M.op (M.op X0 x) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 x X0 X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
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
        have b1e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) (M.op X0 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op (M.op X1 X0) X2) (M.op X0 X0) X3
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 X0 (M.op (M.op x X0) x)
             have i₂ := b1e12 X0 x x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : x = (M.op y x) := by
          first
          | (have i₁ := b1e32 (M.op y x)
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e32
          | exact resolve b1e32 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e39 : ∀ X0 : G, x = (M.op (M.op x x) (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 x y X0
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e12
          | exact resolve b1e12 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e40 : ∀ X0 : G, x = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e39 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e39
          | exact resolve b1e39 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e41 : (M.op x y) = (k x y) := by grind
        have b1e45 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (M.op X0 X0) X1
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e12
          | exact resolve b1e12 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e53 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e48
        have b1e54 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e53
             have r₂ := b1e21
             grind)
          | exact resolve b1e53 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e56 : (σ x) = (σ (k x y)) := by
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
        have b1e58 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e56
          | exact resolve b1e56 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e67 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X0) X3)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 X2 X3
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e12 X1 X1 X2
             have i₂ := b1e17 X1 X1
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X0 X1
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e71 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e24
             have i₂ := b1e17 (σ x) X0
             grind)
          | (have i₁ := b1e24
             have i₂ := b1e17 (σ x) (σ x)
             grind)
          | exact superpose b1e17 b1e24
          | (have j1 := b1e17 (σ x) X0
             grind)
          | (have r₁ := b1e24
             have r₂ := b1e17 (σ x) (σ (M.op x y))
             grind)
          | exact resolve b1e24 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e16 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X0 X1
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 (M.op X0 X1)
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e78 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e78 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e81 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e71 X0
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e71
          | (have j0 := b1e71 X0
             grind)
          | exact resolve b1e71 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e84 : (M.op x y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op x y)
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e13
          | exact resolve b1e13 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e85 : x = (M.op x y) := by
          first
          | (have i₁ := b1e84
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e84
          | exact resolve b1e84 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e101 : x = (M.op y y) := by
          first
          | (have i₁ := b1e40 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e40
          | exact resolve b1e40 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e112 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e117 : y = (M.op x y) := by
          first
          | (have i₁ := b1e34 y
             have i₂ := b1e101
             grind)
          | exact superpose b1e101 b1e34
          | exact resolve b1e34 b1e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e124 : x = y := by
          first
          | (have i₁ := b1e117
             have i₂ := b1e85
             grind)
          | exact superpose b1e85 b1e117
          | exact resolve b1e117 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85 b1e117
        have b1e131 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 x) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e31 X0 X1
             have i₂ := b1e124
             grind)
          | exact superpose b1e124 b1e31
          | exact resolve b1e31 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e222 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        clear b1e79
        have b1e236 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e222 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e222
        have b1e374 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) X2) = (M.op (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e33 (M.op X0 X0) X1 X2 X0
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e33
          | exact resolve b1e33 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e390 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X3) = (M.op (M.op (M.op X1 X3) (M.op X1 X3)) (M.op (M.op (M.op X0 X1) X2) X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e12 (M.op X1 X3) (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X4
             have i₂ := b1e33 X1 X0 X2 X3
             grind)
          | exact superpose b1e33 b1e12
          | exact resolve b1e12 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e519 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e33 X1 X0 (M.op X0 X1) X2
             have i₂ := b1e45 (M.op X0 X1) (M.op X0 X1)
             grind)
          | exact superpose b1e45 b1e33
          | exact resolve b1e33 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e520 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X0 X0) X1 X2
             have i₂ := b1e45 X0 X0
             grind)
          | exact superpose b1e45 b1e12
          | exact resolve b1e12 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e523 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e537 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e523 X0
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e523
          | exact resolve b1e523 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e523
        have b1e588 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e537 (M.op X0 X0)
             have i₂ := b1e45 X0 X0
             grind)
          | exact superpose b1e45 b1e537
          | exact resolve b1e537 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e592 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b1e26 X0 (M.op (τ X0) (τ X0))
             have i₂ := b1e537 (τ X0)
             grind)
          | exact superpose b1e537 b1e26
          | exact resolve b1e26 b1e537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e537
        have b1e593 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e592 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e592
          | exact resolve b1e592 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e592
        have b1e650 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (M.op (M.op x X0) x)
             have i₂ := b1e67 X0 X1 x x
             grind)
          | exact superpose b1e67 b1e12
          | (have j1 := b1e67 X0 X1 x x
             grind)
          | exact resolve b1e12 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e842 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b1e25 X0 (M.op (τ X0) (τ X0))
             have i₂ := b1e588 (τ X0)
             grind)
          | exact superpose b1e588 b1e25
          | exact resolve b1e25 b1e588
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e970 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e81 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e81
          | (have j0 := b1e81 (σ x)
             grind)
          | exact resolve b1e81 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81
        have b1e976 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e970
             have r₂ := b1e21
             grind)
          | exact resolve b1e970 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e970
        have b1e977 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e976
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e976
          | exact resolve b1e976 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e976
        have b1e978 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e977
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e977
          | exact resolve b1e977 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e977
        have b1e979 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b1e978
             have r₂ := b1e24
             grind)
          | exact resolve b1e978 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e978
        have b1e1267 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e30
          | exact resolve b1e30 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e1881 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b1e112 X0 (M.op (σ X0) (σ X0))
             have i₂ := b1e588 (σ X0)
             grind)
          | exact superpose b1e588 b1e112
          | exact resolve b1e112 b1e588
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112 b1e588
        have b1e1922 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e236 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2021 : ∀ X0 X1 : G, x ≠ x ∨ x = (k x (M.op (M.op X0 x) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1922 x (M.op (M.op X0 x) X1)
             have i₂ := b1e131 X0 X1
             grind)
          | exact superpose b1e131 b1e1922
          | (have j0 := b1e1922 x (M.op (M.op X0 x) X1)
             grind)
          | (have r₁ := b1e1922 x (M.op (M.op X0 x) X1)
             have r₂ := b1e131 X0 X1
             grind)
          | exact resolve b1e1922 b1e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131
        have b1e2027 : ∀ X0 X1 : G, x = (k x (M.op (M.op X0 x) X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e2021 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2021
        have b1e2353 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e236 X0 (σ (M.op (τ X0) (τ X0)))
             have i₂ := b1e593 X0
             grind)
          | exact superpose b1e593 b1e236
          | exact resolve b1e236 b1e593
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e236 b1e593
        have b1e3643 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X0 X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e520 X1 (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X3
             have i₂ := b1e33 X1 X0 X2 X1
             grind)
          | exact superpose b1e33 b1e520
          | exact resolve b1e520 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e520
        have b1e4326 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e390 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
             have i₂ := b1e34 (M.op X0 X1)
             grind)
          | exact superpose b1e34 b1e390
          | exact resolve b1e390 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e390
        have b1e4540 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e3643 X0 X1 (M.op X0 X1) (M.op X0 X1)
             have i₂ := b1e34 (M.op X0 X1)
             grind)
          | exact superpose b1e34 b1e3643
          | exact resolve b1e3643 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4736 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        clear b1e650
        have b1e4817 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e4736 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4736
        have b1e4887 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (M.op (M.op (M.op X1 X0) X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e4540 (M.op X0 X0) (M.op (M.op X1 X0) X2)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e4540
          | exact resolve b1e4540 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4889 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e4540 (M.op X0 X0) (M.op X0 X1)
             have i₂ := b1e45 X0 X1
             grind)
          | exact superpose b1e45 b1e4540
          | exact resolve b1e4540 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4963 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1922 X0 (M.op X1 X0)
             have i₂ := b1e4540 X1 X0
             grind)
          | exact superpose b1e4540 b1e1922
          | (have j0 := b1e1922 X0 X0
             grind)
          | exact resolve b1e1922 b1e4540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5030 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) X0) = (M.op (M.op (M.op X1 X0) X2) (M.op X1 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e4887 X0 X1 X2
             have i₂ := b1e4889 (M.op X1 X0) X2
             grind)
          | exact superpose b1e4889 b1e4887
          | exact resolve b1e4887 b1e4889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4887
        have b1e5109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e4963 (M.op X0 X0) X1
             have i₂ := b1e45 X0 X0
             grind)
          | exact superpose b1e45 b1e4963
          | (have j0 := b1e4963 X0 X1
             grind)
          | exact resolve b1e4963 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4963
        have b1e8557 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e374 X1 (M.op X1 X1) x
             have i₂ := b1e45 X1 X1
             grind)
          | exact superpose b1e45 b1e374
          | exact resolve b1e374 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e8689 : ∀ X0 X1 X2 : G, x = (k x (M.op (M.op (M.op X0 (M.op x x)) X1) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e2027 (M.op (M.op (M.op X0 (M.op x x)) X1) (M.op (M.op X0 (M.op x x)) X1)) X2
             have i₂ := b1e374 x X0 X1
             grind)
          | exact superpose b1e374 b1e2027
          | exact resolve b1e2027 b1e374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2027
        have b1e8696 : ∀ X0 X1 X2 : G, x = (k x (M.op (M.op (M.op X0 y) X1) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e8689 X0 X1 X2
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8689
          | exact resolve b1e8689 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8689
        have b1e8736 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e8557 X0 X1
             have i₂ := b1e4889 X0 X1
             grind)
          | exact superpose b1e4889 b1e8557
          | exact resolve b1e8557 b1e4889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8557
        have b1e8752 : ∀ X0 X1 X2 : G, x = (k x (M.op (M.op (M.op X0 x) X1) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e8696 X0 X1 X2
             have i₂ := b1e124
             grind)
          | exact superpose b1e124 b1e8696
          | exact resolve b1e8696 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8696
        have b1e8926 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 (M.op (M.op X0 X1) X0) X2
             have i₂ := b1e8736 X0 X1
             grind)
          | exact superpose b1e8736 b1e12
          | exact resolve b1e12 b1e8736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e9321 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X3) X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e3643 (M.op X0 X0) (M.op (M.op X0 X1) X2) X3 X4
             have i₂ := b1e8926 X0 X1 X2
             grind)
          | exact superpose b1e8926 b1e3643
          | exact resolve b1e3643 b1e8926
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3643
        have b1e9323 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e4540 (M.op X0 X0) (M.op (M.op X0 X1) X2)
             have i₂ := b1e8926 X0 X1 X2
             grind)
          | exact superpose b1e8926 b1e4540
          | exact resolve b1e4540 b1e8926
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8926
        have b1e9329 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e9323 X0 X1 X2
             have i₂ := b1e4889 (M.op X0 X1) X2
             grind)
          | exact superpose b1e4889 b1e9323
          | exact resolve b1e9323 b1e4889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9323
        have b1e9330 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X3) X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e9321 X0 X1 X2 X3 X4
             have i₂ := b1e4889 (M.op X0 X1) X2
             grind)
          | exact superpose b1e4889 b1e9321
          | exact resolve b1e9321 b1e4889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9321
        have b1e9356 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X3) X4)) = (M.op (M.op (M.op X0 X1) X2) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e9330 X0 X1 X2 X3 X4
             have i₂ := b1e9329 X0 X1 X2
             grind)
          | exact superpose b1e9329 b1e9330
          | exact resolve b1e9330 b1e9329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9329 b1e9330
        have b1e10921 : ∀ X0 X1 X2 X3 : G, x = (k x (M.op (M.op (M.op (M.op X0 (M.op x x)) X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e8752 (M.op (M.op (M.op X0 (M.op x x)) X1) (M.op (M.op X0 (M.op x x)) X1)) X2 X3
             have i₂ := b1e374 x X0 X1
             grind)
          | exact superpose b1e374 b1e8752
          | exact resolve b1e8752 b1e374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e374 b1e8752
        have b1e11049 : ∀ X0 X1 X2 X3 : G, x = (k x (M.op (M.op (M.op (M.op X0 y) X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e10921 X0 X1 X2 X3
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e10921
          | exact resolve b1e10921 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10921
        have b1e11051 : ∀ X0 X1 X2 X3 : G, x = (k x (M.op (M.op (M.op (M.op X0 x) X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11049 X0 X1 X2 X3
             have i₂ := b1e124
             grind)
          | exact superpose b1e124 b1e11049
          | exact resolve b1e11049 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11049
        have b1e13309 : ∀ X0 X1 X2 X3 : G, x = (k x (M.op (M.op (M.op (M.op x X0) X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11051 (M.op (M.op x X0) x) X1 X2 X3
             have i₂ := b1e8736 x X0
             grind)
          | exact superpose b1e8736 b1e11051
          | exact resolve b1e11051 b1e8736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11051
        have b1e15195 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e4540 (M.op X0 X0) X1
             have i₂ := b1e4817 X0 X1
             grind)
          | exact superpose b1e4817 b1e4540
          | (have j1 := b1e4817 X0 X1
             grind)
          | exact resolve b1e4540 b1e4817
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4540
        have b1e17107 : ∀ X0 X1 X2 X3 : G, x = (M.op x (M.op (M.op (M.op (M.op x X0) X1) X2) X3)) ∨ (M.op x x) = (M.op x (M.op (M.op (M.op (M.op x X0) X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e13309 X0 X1 X2 X3
             have i₂ := b1e15195 (M.op (M.op (M.op (M.op x X0) X1) X2) X3) x
             grind)
          | exact superpose b1e15195 b1e13309
          | (have j1 := b1e15195 (M.op (M.op (M.op (M.op x X0) X1) X2) X3) x
             grind)
          | exact resolve b1e13309 b1e15195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13309 b1e15195
        have b1e17118 : ∀ X0 X1 X2 X3 : G, y = (M.op x (M.op (M.op (M.op (M.op x X0) X1) X2) X3)) ∨ x = (M.op x (M.op (M.op (M.op (M.op x X0) X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e17107 X0 X1 X2 X3
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e17107
          | (have j0 := b1e17107 X0 X1 X2 X3
             grind)
          | exact resolve b1e17107 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17107
        have b1e17185 : ∀ X0 X1 X2 X3 : G, x = (M.op x (M.op (M.op (M.op (M.op x X0) X1) X2) X3)) ∨ x = (M.op x (M.op (M.op (M.op (M.op x X0) X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e17118 X0 X1 X2 X3
             have i₂ := b1e124
             grind)
          | exact superpose b1e124 b1e17118
          | (have j0 := b1e17118 X0 X1 X2 X3
             grind)
          | exact resolve b1e17118 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17118
        have b1e17186 : ∀ X0 X1 X2 X3 : G, x = (M.op x (M.op (M.op (M.op (M.op x X0) X1) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b1e17185 X0 X1 X2 X3
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17185
        have b1e24310 : ∀ X0 : G, (M.op (M.op X0 x) (M.op X0 x)) = (M.op (M.op X0 x) x) := by
          intro X0
          first
          | (have i₁ := b1e519 X0 x (M.op (M.op (M.op (M.op x x) x) x) x)
             have i₂ := b1e17186 x x x x
             grind)
          | exact superpose b1e17186 b1e519
          | exact resolve b1e519 b1e17186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17186
        have b1e24416 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e34 (M.op X0 X1)
             have i₂ := b1e519 X0 X1 X2
             grind)
          | (have i₁ := b1e34 (M.op X2 X2)
             have i₂ := b1e519 X2 X2 X2
             grind)
          | exact superpose b1e519 b1e34
          | exact resolve b1e34 b1e519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24417 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e45 (M.op X0 X1) X3
             have i₂ := b1e519 X0 X1 X2
             grind)
          | (have i₁ := b1e45 (M.op X2 X2) X1
             have i₂ := b1e519 X2 X2 X2
             grind)
          | exact superpose b1e519 b1e45
          | exact resolve b1e45 b1e519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e519
        have b1e24715 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e24417 X0 X1 X2 x
             have i₂ := b1e9356 X0 X1 (M.op X1 X2) X1 x
             grind)
          | exact superpose b1e9356 b1e24417
          | exact resolve b1e24417 b1e9356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24417
        have b1e24716 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e24416 X0 X1 X2
             have i₂ := b1e5030 X1 X0 (M.op X1 X2)
             grind)
          | exact superpose b1e5030 b1e24416
          | exact resolve b1e24416 b1e5030
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5030 b1e24416
        have b1e24729 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 x) X0) := by
          intro X0
          first
          | (have i₁ := b1e24310 X0
             have i₂ := b1e4889 X0 x
             grind)
          | exact superpose b1e4889 b1e24310
          | exact resolve b1e24310 b1e4889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24310
        have b1e25131 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) x) X0) := by
          intro X0
          first
          | (have i₁ := b1e8736 X0 x
             have i₂ := b1e24729 X0
             grind)
          | (have i₁ := b1e8736 x x
             have i₂ := b1e24729 x
             grind)
          | exact superpose b1e24729 b1e8736
          | exact resolve b1e8736 b1e24729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8736 b1e24729
        have b1e27688 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (M.op X1 (M.op X0 X0)) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e24715 X1 (M.op X0 X0) X0
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e24715
          | exact resolve b1e24715 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e28950 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e24716 (M.op X0 X0) X1 X2
             have i₂ := b1e4817 X0 X1
             grind)
          | exact superpose b1e4817 b1e24716
          | (have j1 := b1e4817 X0 X1
             grind)
          | exact resolve b1e24716 b1e4817
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4817 b1e24716
        have b1e66298 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e4326 X2 X0 X1
             have i₂ := b1e4889 X0 X1
             grind)
          | exact superpose b1e4889 b1e4326
          | exact resolve b1e4326 b1e4889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4326 b1e4889
        have b1e68119 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X0) X3)) (M.op (M.op X0 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e24715 (M.op (M.op X0 X1) X0) (M.op X2 X0) X2
             have i₂ := b1e66298 X0 X1 X2
             grind)
          | exact superpose b1e66298 b1e24715
          | exact resolve b1e24715 b1e66298
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24715 b1e66298
        have b1e68130 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X0) X3)) X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e68119 X0 X1 X2 X3
             have i₂ := b1e9356 X0 X1 (M.op (M.op X2 X0) X3) X1 X0
             grind)
          | exact superpose b1e9356 b1e68119
          | exact resolve b1e68119 b1e9356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9356 b1e68119
        have b1e130440 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X1 X1))) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e68130 X1 X2 (M.op X0 (M.op X1 X1)) X0
             have i₂ := b1e27688 X1 X0
             grind)
          | exact superpose b1e27688 b1e68130
          | exact resolve b1e68130 b1e27688
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27688 b1e68130
        have b1e347738 : x = (M.op (M.op x x) (σ (M.op (τ x) (τ x)))) ∨ x = (σ (M.op (τ x) (τ x))) := by
          first
          | (have i₁ := b1e25131 (σ (M.op (τ x) (τ x)))
             have i₂ := b1e2353 x
             grind)
          | exact superpose b1e2353 b1e25131
          | (have j1 := b1e2353 x
             grind)
          | exact resolve b1e25131 b1e2353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2353 b1e25131
        have b1e347756 : x = (M.op y (σ (M.op (τ x) (τ x)))) ∨ x = (σ (M.op (τ x) (τ x))) := by
          first
          | (have i₁ := b1e347738
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e347738
          | exact resolve b1e347738 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e347738
        have b1e347768 : x = (M.op x (σ (M.op (τ x) (τ x)))) ∨ x = (σ (M.op (τ x) (τ x))) := by
          first
          | (have i₁ := b1e347756
             have i₂ := b1e124
             grind)
          | exact superpose b1e124 b1e347756
          | exact resolve b1e347756 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124 b1e347756
        have b1e390954 : x ≠ x ∨ x = (k x (σ (M.op (τ x) (τ x)))) ∨ x = (σ (M.op (τ x) (τ x))) := by
          first
          | (have i₁ := b1e1922 x (σ (M.op (τ x) (τ x)))
             have i₂ := b1e347768
             grind)
          | exact superpose b1e347768 b1e1922
          | (have j0 := b1e1922 x (σ (M.op (τ x) (τ x)))
             grind)
          | (have r₁ := b1e1922 x (σ (M.op (τ x) (τ x)))
             have r₂ := b1e347768
             grind)
          | exact resolve b1e1922 b1e347768
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1922 b1e347768
        have b1e391058 : x = (k x (σ (M.op (τ x) (τ x)))) ∨ x = (σ (M.op (τ x) (τ x))) := by grind
        clear b1e390954
        have b1e391076 : x = (σ (M.op (τ x) (τ x))) ∨ x = (σ (M.op (τ x) (τ x))) := by
          first
          | (have i₁ := b1e391058
             have i₂ := b1e842 x
             grind)
          | exact superpose b1e842 b1e391058
          | exact resolve b1e391058 b1e842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e842 b1e391058
        have b1e391077 : x = (σ (M.op (τ x) (τ x))) := by grind
        clear b1e391076
        have b1e391117 : (τ x) = (M.op (τ x) (τ x)) := by
          first
          | (have i₁ := b1e13 (M.op (τ x) (τ x))
             have i₂ := b1e391077
             grind)
          | exact superpose b1e391077 b1e13
          | exact resolve b1e13 b1e391077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e391077
        have b1e391232 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (τ x) = (k (τ x) (M.op X0 (τ x))) := by
          intro X0
          first
          | (have i₁ := b1e5109 (τ x) x
             have i₂ := b1e391117
             grind)
          | exact superpose b1e391117 b1e5109
          | (have r₁ := b1e5109 (τ x) x
             have r₂ := b1e391117
             grind)
          | exact resolve b1e5109 b1e391117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5109 b1e391117
        have b1e391640 : ∀ X0 : G, (τ x) = (k (τ x) (M.op X0 (τ x))) := by
          intro X0
          first
          | (have j0 := b1e391232 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e391232
        have b1e391859 : ∀ X0 : G, (σ (τ x)) = (k x (σ (M.op X0 (τ x)))) := by
          intro X0
          first
          | (have i₁ := b1e25 x (M.op X0 (τ x))
             have i₂ := b1e391640 X0
             grind)
          | exact superpose b1e391640 b1e25
          | exact resolve b1e25 b1e391640
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e391640
        have b1e391885 : ∀ X0 : G, x = (k x (σ (M.op X0 (τ x)))) := by
          intro X0
          first
          | (have i₁ := b1e391859 X0
             have i₂ := b1e14 x
             grind)
          | exact superpose b1e14 b1e391859
          | exact resolve b1e391859 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e391859
        have b1e391924 : ∀ X0 : G, (k (τ x) X0) = (M.op (τ x) X0) ∨ x = (k x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e391885 (M.op X0 (M.op (τ x) x))
             have i₂ := b1e28950 X0 (τ x) x
             grind)
          | exact superpose b1e28950 b1e391885
          | (have j1 := b1e28950 X0 (τ x) x
             grind)
          | exact resolve b1e391885 b1e28950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28950
        have b1e391953 : ∀ X0 : G, x = (k x (σ (M.op (τ x) X0))) := by
          intro X0
          first
          | (have i₁ := b1e391885 (M.op (M.op (τ x) X0) (M.op x (M.op (τ x) (τ x))))
             have i₂ := b1e130440 x (τ x) X0
             grind)
          | exact superpose b1e130440 b1e391885
          | exact resolve b1e391885 b1e130440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e130440 b1e391885
        have b1e411626 : ∀ X0 : G, (τ (k x X0)) = (M.op (τ x) (τ X0)) ∨ x = (k x (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e1267 X0 x
             have i₂ := b1e391924 (τ X0)
             grind)
          | exact superpose b1e391924 b1e1267
          | (have j1 := b1e391924 (τ X0)
             grind)
          | exact resolve b1e1267 b1e391924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1267 b1e391924
        have b1e411631 : ∀ X0 : G, (τ (k x X0)) = (M.op (τ x) (τ X0)) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e411626 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e411626
          | (have j0 := b1e411626 X0
             grind)
          | exact resolve b1e411626 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e411626
        have b1e414898 : ∀ X0 : G, x = (k x (σ (τ (k x X0)))) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e391953 (τ X0)
             have i₂ := b1e411631 X0
             grind)
          | exact superpose b1e411631 b1e391953
          | (have j1 := b1e411631 (σ (τ (k x X0)))
             grind)
          | exact resolve b1e391953 b1e411631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e391953 b1e411631
        have b1e414993 : ∀ X0 : G, x = (k x (k x X0)) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e414898 X0
             have i₂ := b1e14 (k x X0)
             grind)
          | exact superpose b1e14 b1e414898
          | (have j0 := b1e414898 (k x X0)
             grind)
          | exact resolve b1e414898 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e414898
        have b1e415410 : x = (k x (τ (M.op (σ x) (σ x)))) ∨ x = (τ (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e414993 (τ (M.op (σ x) (σ x)))
             have i₂ := b1e1881 x
             grind)
          | exact superpose b1e1881 b1e414993
          | (have j0 := b1e414993 (τ (M.op (σ x) (σ x)))
             grind)
          | exact resolve b1e414993 b1e1881
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e414993
        have b1e415445 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e415410
             have i₂ := b1e1881 x
             grind)
          | exact superpose b1e1881 b1e415410
          | exact resolve b1e415410 b1e1881
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1881 b1e415410
        have b1e415446 : x = (τ (M.op (σ x) (σ x))) := by grind
        clear b1e415445
        have b1e415466 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e14 (M.op (σ x) (σ x))
             have i₂ := b1e415446
             grind)
          | exact superpose b1e415446 b1e14
          | exact resolve b1e14 b1e415446
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e415446
        have b1e415497 : False := by grind
        exact b1e415497
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e39 : (M.op x y) = (k x y) := by grind
        have b2e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e765 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e55 x y
             grind)
          | exact superpose b2e55 b2e22
          | (have j1 := b2e55 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e55 x y
             grind)
          | exact resolve b2e22 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e837 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        clear b2e765
        have b2e846 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e837
             have r₂ := b2e21
             grind)
          | exact resolve b2e837 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e837
        have b2e852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e846
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e846
          | exact resolve b2e846 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e846
        have b2e853 : False := by grind
        exact b2e853
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e29 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 X0 (M.op (M.op x X0) x)
             have i₂ := b3e12 X0 x x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e31 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e31
          | exact resolve b3e31 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op X0 X0) X1
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e12
          | exact resolve b3e12 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e36 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b3e39 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ x = (k x y) := by
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
        have b3e44 : y = (M.op x x) ∨ x = (k x y) := by grind
        clear b3e39
        have b3e47 : x = (k x y) := by
          first
          | (have r₁ := b3e44
             have r₂ := b3e20
             grind)
          | exact resolve b3e44 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b3e64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e16 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 (M.op X0 X1)
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e69 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69
        have b3e81 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e34 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e34
          | exact resolve b3e34 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e89 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b3e90 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e31 (M.op X0 X0)
             have i₂ := b3e34 X0 X0
             grind)
          | exact superpose b3e34 b3e31
          | exact resolve b3e31 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e96 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e89 X0
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e89
          | exact resolve b3e89 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e89
        have b3e107 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e96 (M.op X0 X0)
             have i₂ := b3e34 X0 X0
             grind)
          | exact superpose b3e34 b3e96
          | exact resolve b3e96 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e117 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e26 X1 X0
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e139 : (σ (M.op x x)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e36
             grind)
          | exact superpose b3e36 b3e24
          | exact resolve b3e24 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e36
        have b3e145 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e139
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e139
          | exact resolve b3e139 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e139
        have b3e161 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e96 (σ y)
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e96
          | exact resolve b3e96 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e96
        have b3e167 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e161
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e161
          | exact resolve b3e161 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e161
        have b3e170 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e167
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e167
          | exact resolve b3e167 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e167
        have b3e185 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e29 X0
             have i₂ := b3e170
             grind)
          | exact superpose b3e170 b3e29
          | exact resolve b3e29 b3e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e186 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e170
             grind)
          | exact superpose b3e170 b3e32
          | exact resolve b3e32 b3e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e170
        have b3e292 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        clear b3e70
        have b3e310 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e292 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e292
        have b3e1167 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e2083 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e310 (σ X1) (σ X0)
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e310
          | exact resolve b3e310 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2106 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e310 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e310
        have b3e2146 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e2106 (σ x) (M.op (σ x) X0)
             have i₂ := b3e185 X0
             grind)
          | exact superpose b3e185 b3e2106
          | (have j0 := b3e2106 (σ x) (M.op (σ x) X0)
             grind)
          | (have r₁ := b3e2106 (σ x) (M.op (σ x) X0)
             have r₂ := b3e185 X0
             grind)
          | exact resolve b3e2106 b3e185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e185 b3e2106
        have b3e2150 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have j0 := b3e2146 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2146
        have b3e2364 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b3e117 x (M.op (σ x) X0)
             have i₂ := b3e2150 X0
             grind)
          | exact superpose b3e2150 b3e117
          | exact resolve b3e117 b3e2150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117 b3e2150
        have b3e2375 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b3e2364 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e2364
          | exact resolve b3e2364 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2364
        have b3e15231 : ∀ X0 : G, (σ x) ≠ (σ (k x X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
          intro X0
          first
          | (have i₁ := b3e1167 x x
             have i₂ := b3e186
             grind)
          | exact superpose b3e186 b3e1167
          | (have j0 := b3e1167 x X0
             grind)
          | exact resolve b3e1167 b3e186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e186 b3e1167
        have b3e15254 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
          intro X0
          first
          | (have j0 := b3e15231 X0
             have j1 := b3e2083 x X0
             grind)
          | (have r₁ := b3e15231 x
             have r₂ := b3e2083 x x
             grind)
          | exact resolve b3e15231 b3e2083
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2083 b3e15231
        have b3e59678 : ∀ X0 : G, x = (k x (τ (σ (k x X0)))) ∨ (σ X0) = (σ x) := by
          intro X0
          first
          | (have i₁ := b3e2375 (σ X0)
             have i₂ := b3e15254 X0
             grind)
          | exact superpose b3e15254 b3e2375
          | (have j1 := b3e15254 X0
             grind)
          | exact resolve b3e2375 b3e15254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2375 b3e15254
        have b3e59844 : ∀ X0 : G, x = (k x (k x X0)) ∨ (σ X0) = (σ x) := by
          intro X0
          first
          | (have i₁ := b3e59678 X0
             have i₂ := b3e13 (k x X0)
             grind)
          | exact superpose b3e13 b3e59678
          | (have j0 := b3e59678 X0
             grind)
          | exact resolve b3e59678 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59678
        have b3e60928 : x = (k x (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e59844 (M.op x x)
             have i₂ := b3e107 x
             grind)
          | exact superpose b3e107 b3e59844
          | (have j0 := b3e59844 (M.op x x)
             grind)
          | exact resolve b3e59844 b3e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e107 b3e59844
        have b3e60993 : x = (k x (M.op x x)) := by
          first
          | (have r₁ := b3e60928
             have r₂ := b3e145
             grind)
          | exact resolve b3e60928 b3e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60928
        have b3e60997 : x = (M.op x (M.op x x)) := by grind
        clear b3e60993
        have b3e61001 : x = (M.op x x) := by
          first
          | (have i₁ := b3e60997
             have i₂ := b3e90 x
             grind)
          | exact superpose b3e90 b3e60997
          | exact resolve b3e60997 b3e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90 b3e60997
        have b3e63526 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e145
             have i₂ := b3e61001
             grind)
          | exact superpose b3e61001 b3e145
          | exact resolve b3e145 b3e61001
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e145 b3e61001
        have b3e63658 : False := by grind
        exact b3e63658
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X1 X0) X2) (M.op X0 X0) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 X0 (M.op (M.op x X0) x)
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X0 X0) X1
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e32 (M.op X0 X0)
               have i₂ := b4e34 X0 X0
               grind)
            | exact superpose b4e34 b4e32
            | exact resolve b4e32 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X0 X0) X1 X2
               have i₂ := b4e34 X0 X0
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b4e47 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e46 X0
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e46
            | exact resolve b4e46 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X0) X3)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X2 X3
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e13 X1 X1 X2
               have i₂ := b4e18 X1 X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 X1
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 (M.op X0 X1)
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e85 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85
          have b4e93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e92 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e104 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b4e108 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b4e109 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b4e104 X0
               have i₂ := b4e43 (τ X0)
               grind)
            | exact superpose b4e43 b4e104
            | exact resolve b4e104 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104
          have b4e122 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          clear b4e29
          have b4e193 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b4e108 (M.op (σ X0) (σ X0)) X0
               have i₂ := b4e47 (σ X0)
               grind)
            | exact superpose b4e47 b4e108
            | exact resolve b4e108 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47 b4e108
          have b4e199 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e193 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e193
            | exact resolve b4e193 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193
          have b4e214 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            grind
          clear b4e93
          have b4e234 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e214 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214
          have b4e351 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X3) = (M.op (M.op (M.op X1 X3) (M.op X1 X3)) (M.op (M.op (M.op X0 X1) X2) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 (M.op X1 X3) (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X4
               have i₂ := b4e31 X1 X0 X2 X3
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e537 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (M.op (M.op x X0) x)
               have i₂ := b4e72 X0 X1 x x
               grind)
            | exact superpose b4e72 b4e13
            | (have j1 := b4e72 X0 X1 x x
               grind)
            | exact resolve b4e13 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e716 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e234 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1102 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e44 X1 (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X3
               have i₂ := b4e31 X1 X0 X2 X1
               grind)
            | exact superpose b4e31 b4e44
            | exact resolve b4e44 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1882 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e234 (σ (M.op (τ X0) (τ X0))) X0
               have i₂ := b4e109 X0
               grind)
            | exact superpose b4e109 b4e234
            | exact resolve b4e234 b4e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109 b4e234
          have b4e2298 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1102 (M.op X0 X0) X0 X1 X2
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e1102
            | exact resolve b4e1102 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2347 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1102 X0 X1 (M.op X0 X1) (M.op X0 X1)
               have i₂ := b4e32 (M.op X0 X1)
               grind)
            | exact superpose b4e32 b4e1102
            | exact resolve b4e1102 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2472 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (M.op (M.op (M.op X1 X0) X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2347 (M.op X0 X0) (M.op (M.op X1 X0) X2)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e2347
            | exact resolve b4e2347 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2474 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e2347 (M.op X0 X0) (M.op X0 X1)
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e2347
            | exact resolve b4e2347 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2508 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 (M.op X1 X0)
               have i₂ := b4e2347 X1 X0
               grind)
            | exact superpose b4e2347 b4e17
            | (have j0 := b4e17 X0 (M.op X1 X0)
               grind)
            | (have r₁ := b4e17 X1 (M.op X0 X1)
               have r₂ := b4e2347 X0 X1
               grind)
            | exact resolve b4e17 b4e2347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2523 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e716 X0 (M.op X1 X0)
               have i₂ := b4e2347 X1 X0
               grind)
            | exact superpose b4e2347 b4e716
            | (have j0 := b4e716 X0 X0
               grind)
            | exact resolve b4e716 b4e2347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e716
          have b4e2554 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e2508 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2508
          have b4e2558 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) X0) = (M.op (M.op (M.op X1 X0) X2) (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2472 X0 X1 X2
               have i₂ := b4e2474 (M.op X1 X0) X2
               grind)
            | exact superpose b4e2474 b4e2472
            | exact resolve b4e2472 b4e2474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2472
          have b4e3065 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2523 (M.op X0 X0) X1
               have i₂ := b4e34 X0 X0
               grind)
            | exact superpose b4e34 b4e2523
            | (have j0 := b4e2523 X0 X1
               grind)
            | exact resolve b4e2523 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2523
          have b4e3417 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e351 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
               have i₂ := b4e32 (M.op X0 X1)
               grind)
            | exact superpose b4e32 b4e351
            | exact resolve b4e351 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e351
          have b4e3500 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) X1) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e3417 X0 X1 X2
               have i₂ := b4e2474 X1 X2
               grind)
            | exact superpose b4e2474 b4e3417
            | exact resolve b4e3417 b4e2474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3417
          have b4e3661 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e3500 (M.op X0 X0) (M.op X0 X1) X2
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e3500
            | exact resolve b4e3500 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3662 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e3500 (M.op X0 X0) X0 X1
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e3500
            | exact resolve b4e3500 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3701 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e31 X1 X0 X0 X2
               have i₂ := b4e3500 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b4e3500 b4e31
            | exact resolve b4e31 b4e3500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e3728 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 (M.op (M.op X1 x) X1)
               have i₂ := b4e3500 (M.op X1 x) X1 x
               grind)
            | exact superpose b4e3500 b4e43
            | exact resolve b4e43 b4e3500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3500
          have b4e3785 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e3728 X0 X1
               have i₂ := b4e2558 X1 X0 X0
               grind)
            | exact superpose b4e2558 b4e3728
            | exact resolve b4e3728 b4e2558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3728
          have b4e3808 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op X0 X1) X2) X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e3661 X0 X1 X2
               have i₂ := b4e2558 X1 X0 X2
               grind)
            | exact superpose b4e2558 b4e3661
            | exact resolve b4e3661 b4e2558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2558 b4e3661
          have b4e3972 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          clear b4e537
          have b4e4053 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e3972 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3972
          have b4e4160 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (M.op (M.op X0 X1) X0) X2
               have i₂ := b4e3662 X0 X1
               grind)
            | exact superpose b4e3662 b4e13
            | exact resolve b4e13 b4e3662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4181 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e1102 (M.op (M.op X0 X1) X0) X0 X2 X3
               have i₂ := b4e3662 X0 X1
               grind)
            | exact superpose b4e3662 b4e1102
            | exact resolve b4e1102 b4e3662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1102 b4e3662
          have b4e4784 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2347 (M.op X0 X0) (M.op (M.op X0 X1) X2)
               have i₂ := b4e4160 X0 X1 X2
               grind)
            | exact superpose b4e4160 b4e2347
            | exact resolve b4e2347 b4e4160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2347 b4e4160
          have b4e4793 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e4784 X0 X1 X2
               have i₂ := b4e2474 (M.op X0 X1) X2
               grind)
            | exact superpose b4e2474 b4e4784
            | exact resolve b4e4784 b4e2474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4784
          have b4e5403 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e3701 X0 (M.op (M.op X0 X1) X2) X2
               have i₂ := b4e2298 X0 X1 X2
               grind)
            | exact superpose b4e2298 b4e3701
            | exact resolve b4e3701 b4e2298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2298
          have b4e5514 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e3785 X0 X1
               have i₂ := b4e3701 X0 X1 X2
               grind)
            | (have i₁ := b4e3785 (M.op X1 X2) X1
               have i₂ := b4e3701 (M.op X1 X2) X1 X2
               grind)
            | exact superpose b4e3701 b4e3785
            | exact resolve b4e3785 b4e3701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3785
          have b4e5732 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) X2) X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e5403 X0 X1 X2 X3
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e5403
            | exact resolve b4e5403 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5403
          have b4e6795 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e3701 X0 (M.op (M.op (M.op X0 X1) X2) X3) X2
               have i₂ := b4e4181 X0 X1 X2 X3
               grind)
            | exact superpose b4e4181 b4e3701
            | exact resolve b4e3701 b4e4181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3701 b4e4181
          have b4e6844 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) = X0 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e6795 X0 X1 X2 X3 X4
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e6795
            | exact resolve b4e6795 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e6795
          have b4e14443 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e44 (M.op (M.op X0 X1) X2) (M.op X0 X0) X3
               have i₂ := b4e5732 X0 X1 X2 (M.op (M.op X0 X1) X2)
               grind)
            | exact superpose b4e5732 b4e44
            | exact resolve b4e44 b4e5732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e5732
          have b4e14521 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X3)) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e14443 X0 X1 X2 X3
               have i₂ := b4e2474 (M.op X0 X1) X2
               grind)
            | exact superpose b4e2474 b4e14443
            | exact resolve b4e14443 b4e2474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14443
          have b4e14561 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X3)) = (M.op (M.op (M.op X0 X1) X2) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e14521 X0 X1 X2 X3
               have i₂ := b4e4793 X0 X1 X2
               grind)
            | exact superpose b4e4793 b4e14521
            | exact resolve b4e14521 b4e4793
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4793 b4e14521
          have b4e17301 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e5514 (M.op X0 X0) X1 X2
               have i₂ := b4e4053 X0 X1
               grind)
            | exact superpose b4e4053 b4e5514
            | (have j1 := b4e4053 X0 X1
               grind)
            | exact resolve b4e5514 b4e4053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4053 b4e5514
          have b4e19742 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 (M.op X1 (τ X0))
               have i₂ := b4e2554 (τ X0) X1
               grind)
            | exact superpose b4e2554 b4e28
            | (have j1 := b4e2554 (τ X0) X1
               grind)
            | exact resolve b4e28 b4e2554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e2554
          have b4e19759 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19742 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e19742
            | (have j0 := b4e19742 X0 X1
               grind)
            | exact resolve b4e19742 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19742
          have b4e63019 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X5) = (M.op (M.op (M.op X0 X5) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) (M.op X0 X0)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e3808 (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X2
               have i₂ := b4e6844 X0 X1 X2 X3 X4
               grind)
            | exact superpose b4e6844 b4e3808
            | exact resolve b4e3808 b4e6844
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3808 b4e6844
          have b4e63064 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X5) = (M.op (M.op (M.op X0 X5) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) X0) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e63019 X0 X1 X2 X3 X4 X5
               have i₂ := b4e14561 X0 X5 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X0
               grind)
            | exact superpose b4e14561 b4e63019
            | exact resolve b4e63019 b4e14561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14561 b4e63019
          have b4e303362 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1882 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e1882
            | exact resolve b4e1882 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1882
          have b4e391632 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (M.op X1 X0))) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19759 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e19759
            | exact resolve b4e19759 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19759
          have b4e391658 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X0))) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e391632 X0 X1
               have i₂ := b4e19 X0 (M.op X1 X0)
               grind)
            | exact superpose b4e19 b4e391632
            | (have j0 := b4e391632 X0 X1
               grind)
            | exact resolve b4e391632 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e391632
          have b4e391663 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e391658 X1 (M.op X0 (M.op X1 x))
               have i₂ := b4e17301 X0 X1 x
               grind)
            | exact superpose b4e17301 b4e391658
            | (have j1 := b4e17301 X0 X1 x
               grind)
            | exact resolve b4e391658 b4e17301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17301 b4e391658
          have b4e428903 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          clear b4e391663
          have b4e428918 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e428903 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428903
          have b4e428925 : ∀ X0 : G, (σ X0) = (σ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e428918 X0 (τ (M.op (σ X0) (σ X0)))
               have i₂ := b4e199 X0
               grind)
            | exact superpose b4e199 b4e428918
            | exact resolve b4e428918 b4e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e199 b4e428918
          have b4e428949 : ∀ X0 : G, (M.op (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e428925 X0
               have i₂ := b4e15 (M.op (σ X0) (σ X0))
               grind)
            | exact superpose b4e15 b4e428925
            | (have j0 := b4e428925 X0
               grind)
            | exact resolve b4e428925 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428925
          have b4e429377 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e428949 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e428949
            | exact resolve b4e428949 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428949
          have b4e429439 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e429377 (M.op x x)
               have i₂ := b4e34 x x
               grind)
            | exact superpose b4e34 b4e429377
            | (have j0 := b4e429377 X0
               grind)
            | exact resolve b4e429377 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e429451 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e2474 (τ (M.op X0 X0)) (τ X0)
               have i₂ := b4e429377 X0
               grind)
            | exact superpose b4e429377 b4e2474
            | (have j1 := b4e429377 X0
               grind)
            | exact resolve b4e2474 b4e429377
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2474 b4e429377
          have b4e431170 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e429439 X0
               have i₂ := b4e429451 X0
               grind)
            | exact superpose b4e429451 b4e429439
            | (have j0 := b4e429439 X0
               have j1 := b4e429451 X0
               grind)
            | exact resolve b4e429439 b4e429451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e429439 b4e429451
          have b4e431180 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e431170 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e431170
          have b4e431182 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e431180 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e431180
            | (have j0 := b4e431180 (σ X0)
               grind)
            | exact resolve b4e431180 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e431180
          have b4e436216 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op (σ X0) (σ X0))
               have i₂ := b4e431182 X0
               grind)
            | exact superpose b4e431182 b4e15
            | (have j1 := b4e431182 X0
               grind)
            | exact resolve b4e15 b4e431182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e431182
          have b4e436423 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e436216 x
               grind)
            | exact superpose b4e436216 b4e27
            | (have j1 := b4e436216 x
               grind)
            | (have r₁ := b4e27
               have r₂ := b4e436216 x
               grind)
            | exact resolve b4e27 b4e436216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e436216
          have b4e436437 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e436423
          have b4e436455 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e436437
               grind)
            | exact superpose b4e436437 b4e27
            | exact resolve b4e27 b4e436437
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e436530 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e3065 (σ x) x
               have i₂ := b4e436437
               grind)
            | exact superpose b4e436437 b4e3065
            | (have r₁ := b4e3065 (σ x) x
               have r₂ := b4e436437
               grind)
            | exact resolve b4e3065 b4e436437
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3065 b4e436437
          have b4e436969 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have j0 := b4e436530 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e436530
          have b4e437921 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b4e122 x (M.op X0 (σ x))
               have i₂ := b4e436969 X0
               grind)
            | exact superpose b4e436969 b4e122
            | exact resolve b4e122 b4e436969
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122 b4e436969
          have b4e437945 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b4e437921 X0
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e437921
            | exact resolve b4e437921 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e437921
          have b4e438014 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) := by
            intro X0
            first
            | (have i₁ := b4e437945 (M.op (M.op (σ x) X0) (M.op (M.op (M.op (M.op (σ x) x) x) x) x))
               have i₂ := b4e63064 (σ x) x x x x X0
               grind)
            | exact superpose b4e63064 b4e437945
            | exact resolve b4e437945 b4e63064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63064 b4e437945
          have b4e438191 : x = (k x (τ (σ (M.op x x)))) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e438014 (σ (M.op x x))
               have i₂ := b4e303362 x
               grind)
            | exact superpose b4e303362 b4e438014
            | (have j1 := b4e303362 x
               grind)
            | exact resolve b4e438014 b4e303362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e303362 b4e438014
          have b4e438265 : x = (k x (τ (σ (M.op x x)))) := by
            first
            | (have r₁ := b4e438191
               have r₂ := b4e436455
               grind)
            | exact resolve b4e438191 b4e436455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e438191
          have b4e438273 : x = (k x (M.op x x)) := by
            first
            | (have i₁ := b4e438265
               have i₂ := b4e14 (M.op x x)
               grind)
            | exact superpose b4e14 b4e438265
            | exact resolve b4e438265 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e438265
          have b4e438275 : x = (M.op x (M.op x x)) := by grind
          clear b4e438273
          have b4e438277 : x = (M.op x x) := by
            first
            | (have i₁ := b4e438275
               have i₂ := b4e43 x
               grind)
            | exact superpose b4e43 b4e438275
            | exact resolve b4e438275 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e438275
          have b4e438343 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e436455
               have i₂ := b4e438277
               grind)
            | exact superpose b4e438277 b4e436455
            | exact resolve b4e436455 b4e438277
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e436455 b4e438277
          have b4e438936 : False := by grind
          exact b4e438936
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X1 X0) X2) (M.op X0 X0) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 X0 (M.op (M.op x X0) x)
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X0 X0) X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X0 X0) X1 X2
               have i₂ := b5e33 X0 X0
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e47 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e51 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e47
          have b5e54 : x = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e21
               grind)
            | exact resolve b5e51 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b5e777 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e63 x y
               grind)
            | exact superpose b5e63 b5e24
            | (have j1 := b5e63 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e63 x y
               grind)
            | exact resolve b5e24 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e854 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b5e777
          have b5e864 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e854
               have r₂ := b5e23
               grind)
            | exact resolve b5e854 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e854
          have b5e871 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e864
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e864
            | exact resolve b5e864 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e864
          have b5e959 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 (σ y) (σ x) X0
               have i₂ := b5e871
               grind)
            | exact superpose b5e871 b5e13
            | exact resolve b5e13 b5e871
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1617 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e41 X1 (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X3
               have i₂ := b5e30 X1 X0 X2 X1
               grind)
            | exact superpose b5e30 b5e41
            | exact resolve b5e41 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e41
          have b5e2276 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
            first
            | (have i₁ := b5e959 (σ y)
               have i₂ := b5e871
               grind)
            | exact superpose b5e871 b5e959
            | exact resolve b5e959 b5e871
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e871 b5e959
          have b5e2644 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1617 X0 X1 (M.op X0 X1) (M.op X0 X1)
               have i₂ := b5e31 (M.op X0 X1)
               grind)
            | exact superpose b5e31 b5e1617
            | exact resolve b5e1617 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e1617
          have b5e2839 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e2644 (M.op (σ y) (σ y)) (σ x)
               have i₂ := b5e2276
               grind)
            | exact superpose b5e2276 b5e2644
            | exact resolve b5e2644 b5e2276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2276 b5e2644
          have b5e2921 : False := by grind
          exact b5e2921
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e29 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 X0 (M.op (M.op x X0) x)
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (M.op X0 X0) X1
             have i₂ := b6e29 X0
             grind)
          | exact superpose b6e29 b6e12
          | exact resolve b6e12 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e34 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e33
          | exact resolve b6e33 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e46 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e32 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e32
          | exact resolve b6e32 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        clear b6e32
        have b6e59 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e53 X0
             have i₂ := b6e29 X0
             grind)
          | exact superpose b6e29 b6e53
          | exact resolve b6e53 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29 b6e53
        have b6e139 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e59 (σ y)
             have i₂ := b6e46
             grind)
          | exact superpose b6e46 b6e59
          | exact resolve b6e59 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46 b6e59
        have b6e145 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e139
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e139
          | exact resolve b6e139 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139
        have b6e149 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e34
             grind)
          | exact superpose b6e34 b6e19
          | exact resolve b6e19 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e155 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e149
             have i₂ := b6e145
             grind)
          | exact superpose b6e145 b6e149
          | exact resolve b6e149 b6e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e163 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e145
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e145
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e145 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e145
        have b6e170 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e163
             have r₂ := b6e155
             grind)
          | exact resolve b6e163 b6e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e155 b6e163
        have b6e171 : y = (M.op x x) := by
          first
          | (have r₁ := b6e170
             have r₂ := b6e21
             grind)
          | exact resolve b6e170 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e170
        have b6e172 : False := by grind
        exact b6e172
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 X0 (M.op (M.op x X0) x)
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op X0 X0) X1
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e13
            | exact resolve b7e13 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X0 X0) X1 X2
               have i₂ := b7e32 X0 X0
               grind)
            | exact superpose b7e32 b7e13
            | exact resolve b7e13 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e51 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e49
          have b7e52 : (σ x) = (k (σ x) (σ y)) := by
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
            | (have i₁ := b7e52
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e52
            | exact resolve b7e52 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e60 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e55
               grind)
            | exact superpose b7e55 b7e14
            | exact resolve b7e14 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e61 : x = (k x y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e60
            | exact resolve b7e60 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e98 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
          have b7e99 : x = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e98
               have r₂ := b7e22
               grind)
            | exact resolve b7e98 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e101 : x = (M.op x y) := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e21
               grind)
            | exact resolve b7e99 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e113 : ∀ X0 : G, y = (M.op (M.op y y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 y x X0
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e13
            | exact resolve b7e13 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e212 : y = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b7e113 y
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e113
            | exact resolve b7e113 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101 b7e113
          have b7e256 : ∀ X0 : G, x = (M.op (M.op x x) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 x (M.op y y) X0
               have i₂ := b7e212
               grind)
            | exact superpose b7e212 b7e13
            | exact resolve b7e13 b7e212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e212
          have b7e1734 : ∀ X0 : G, (M.op y y) = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e41 y (M.op x x) X0
               have i₂ := b7e256 y
               grind)
            | exact superpose b7e256 b7e41
            | exact resolve b7e41 b7e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e256
          have b7e2138 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op y y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e41 x y X0
               have i₂ := b7e1734 x
               grind)
            | exact superpose b7e1734 b7e41
            | exact resolve b7e41 b7e1734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e1734
          have b7e3641 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e2138 y
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e2138
            | exact resolve b7e2138 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e2138
          have b7e3701 : False := by grind
          exact b7e3701
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b8e709 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
            | exact resolve b8e24 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e786 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b8e709
          have b8e796 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e786
               have r₂ := b8e23
               grind)
            | exact resolve b8e786 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e786
          have b8e804 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e796
               grind)
            | exact superpose b8e796 b8e20
            | exact resolve b8e20 b8e796
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e796
          have b8e877 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e804
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e804
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e804 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e804
          have b8e878 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
          clear b8e877
          have b8e882 : y = (M.op x x) := by
            first
            | (have r₁ := b8e878
               have r₂ := b8e22
               grind)
            | exact resolve b8e878 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e878
          have b8e884 : False := by grind
          exact b8e884

/-- `Equation1738`: `x = (y ◇ y) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation1738 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1738 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1738.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e31 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 x X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 X1) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
           have i₂ := b0e10 X0 (M.op (M.op X2 X0) X0) X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)
           have i₂ := b0e10 X0 (M.op (M.op X1 X0) X0) X1
           grind)
        | exact superpose b0e10 b0e31
        | exact resolve b0e31 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e52 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X2)) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X2 X1 X2
           have i₂ := b0e14 X2 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X2 X0)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e14 (σ X1) (σ X0)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X1) (σ X0)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X1 X0
           have i₂ := b0e14 (τ X1) X0
           grind)
        | exact superpose b0e14 b0e23
        | (have j1 := b0e14 (τ X1) X0
           grind)
        | exact resolve b0e23 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e69 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e24 X0 X1
           have i₂ := b0e14 X1 (τ X0)
           grind)
        | exact superpose b0e14 b0e24
        | (have j1 := b0e14 X1 (τ X0)
           grind)
        | exact resolve b0e24 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e83 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e41 (M.op (M.op X0 X1) X1) y
           have i₂ := b0e31 X0 X1
           grind)
        | exact superpose b0e31 b0e41
        | exact resolve b0e41 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e93 : ∀ X0 : G, (M.op X0 (M.op y X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e83 X0 x
           have i₂ := b0e41 X0 x
           grind)
        | exact superpose b0e41 b0e83
        | exact resolve b0e83 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e108 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (σ y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)
           have i₂ := b0e10 X0 (M.op (M.op X1 X0) X0) X1
           grind)
        | exact superpose b0e10 b0e32
        | exact resolve b0e32 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e116 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e108 X0 x
           have i₂ := b0e41 X0 x
           grind)
        | exact superpose b0e41 b0e108
        | exact resolve b0e108 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108
      have b0e161 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X1 x
           have i₂ := b0e36 X1 X0 x
           grind)
        | (have i₁ := b0e41 X0 X0
           have i₂ := b0e36 X0 X0 x
           grind)
        | exact superpose b0e36 b0e41
        | exact resolve b0e41 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e162 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e31 x X1
           have i₂ := b0e36 X1 X0 x
           grind)
        | (have i₁ := b0e31 X0 X0
           have i₂ := b0e36 X0 X0 x
           grind)
        | exact superpose b0e36 b0e31
        | exact resolve b0e31 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e163 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X2 x
           have i₂ := b0e36 X1 X0 x
           grind)
        | (have i₁ := b0e10 X0 X1 X0
           have i₂ := b0e36 X0 X0 X2
           grind)
        | exact superpose b0e36 b0e10
        | exact resolve b0e10 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e254 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e50 (σ X1) (σ X0)
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e50
        | exact resolve b0e50 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e260 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e50 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50
      have b0e395 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      clear b0e52
      have b0e589 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e162 X1 (M.op X1 X1)
           have i₂ := b0e14 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e162 X0 X1
           have i₂ := b0e14 X0 (M.op (M.op X0 X0) X1)
           grind)
        | exact superpose b0e14 b0e162
        | (have j1 := b0e14 X1 (M.op y X0)
           grind)
        | exact resolve b0e162 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e733 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1
           have i₂ := b0e54 X1 X0
           grind)
        | exact superpose b0e54 b0e11
        | (have j1 := b0e54 X1 X0
           grind)
        | exact resolve b0e11 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e747 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X2) = (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X3)) = (σ (k X3 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e36 X2 (σ X3) X1
           have i₂ := b0e54 X0 X3
           grind)
        | exact superpose b0e54 b0e36
        | (have j1 := b0e54 X0 X3
           grind)
        | exact resolve b0e36 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e751 : ∀ X0 X1 X2 : G, (M.op y (M.op (σ X0) X2)) = X2 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e162 (σ X1) X2
           have i₂ := b0e54 X0 X1
           grind)
        | exact superpose b0e54 b0e162
        | (have j1 := b0e54 X0 X1
           grind)
        | exact resolve b0e162 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e162
      have b0e765 : ∀ X0 X2 X3 : G, (M.op y X2) = (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X3)) = (σ (k X3 X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e747 X0 x X2 X3
           have i₂ := b0e41 X2 x
           grind)
        | exact superpose b0e41 b0e747
        | (have j0 := b0e747 X0 x X2 X3
           grind)
        | exact resolve b0e747 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e747
      have b0e1133 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (M.op (M.op X0 X0) (M.op X0 X0)) X1
           have i₂ := b0e163 X0 (M.op X0 X0) (M.op X0 X0)
           grind)
        | exact superpose b0e163 b0e14
        | (have j0 := b0e14 X0 X1
           grind)
        | exact resolve b0e14 b0e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e163
      have b0e1161 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op X0 X0))) = (k (M.op y (M.op X0 X0)) X1) ∨ (M.op X0 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1133 X0 X1
           have i₂ := b0e161 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e161 b0e1133
        | (have j0 := b0e1133 X0 X1
           grind)
        | exact resolve b0e1133 b0e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1133
      have b0e2254 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e69 (σ X0) X1
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e69
        | exact resolve b0e69 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e2254 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e2254
        | (have j0 := b0e2254 X0 X1
           grind)
        | exact resolve b0e2254 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2254
      have b0e2606 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e395 X0
           have i₂ := b0e14 X0 X1
           grind)
        | (have i₁ := b0e395 X0
           have i₂ := b0e14 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e14 b0e395
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e395 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e395
      have b0e2706 : ∀ X0 X1 : G, (σ X0) = (k (σ (τ X1)) X1) ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e69 X1 (τ X1)
           have i₂ := b0e55 X0 X1
           grind)
        | (have i₁ := b0e69 X0 X1
           have i₂ := b0e55 (M.op (τ X0) X1) X1
           grind)
        | exact superpose b0e55 b0e69
        | (have j1 := b0e55 X0 X1
           grind)
        | exact resolve b0e69 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55 b0e69
      have b0e2756 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (σ X0) = (k X1 X1) ∨ (τ X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e2706 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e2706
        | (have j0 := b0e2706 X0 X1
           grind)
        | exact resolve b0e2706 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2706
      have b0e2835 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e254 y x
           grind)
        | exact superpose b0e254 b0e16
        | (have j1 := b0e254 y x
           grind)
        | exact resolve b0e16 b0e254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2841 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k X0 y)) ∨ (σ X0) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e116 (σ X0)
           have i₂ := b0e254 X0 y
           grind)
        | exact superpose b0e254 b0e116
        | (have j1 := b0e254 X0 y
           grind)
        | exact resolve b0e116 b0e254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116 b0e254
      have b0e4502 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e733 X1 X1
           have i₂ := b0e54 X0 X1
           grind)
        | exact superpose b0e54 b0e733
        | (have j0 := b0e733 X1 X0
           have j1 := b0e54 X0 X1
           grind)
        | exact resolve b0e733 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54 b0e733
      have b0e4542 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e4502 X0 X1
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e4502
        | (have j0 := b0e4502 X0 X1
           grind)
        | exact resolve b0e4502 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4502
      have b0e4706 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e765 x (σ y) X0
           grind)
        | exact superpose b0e765 b0e16
        | (have j1 := b0e765 x x X0
           grind)
        | exact resolve b0e16 b0e765
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4759 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e765 x X0 y
           grind)
        | exact superpose b0e765 b0e16
        | (have j1 := b0e765 x X0 x
           grind)
        | exact resolve b0e16 b0e765
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e765
      have b0e29895 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b0e2835
           have i₂ := b0e2359 x y
           grind)
        | exact superpose b0e2359 b0e2835
        | (have j1 := b0e2359 x y
           grind)
        | (have r₁ := b0e2835
           have r₂ := b0e2359 x y
           grind)
        | exact resolve b0e2835 b0e2359
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2835
      have b0e29899 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
      clear b0e29895
      have b0e29912 : (M.op x y) = (τ (σ y)) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b0e11 (M.op x y)
           have i₂ := b0e29899
           grind)
        | exact superpose b0e29899 b0e11
        | exact resolve b0e11 b0e29899
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29899
      have b0e30053 : x = (M.op y y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e29912
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e29912
        | exact resolve b0e29912 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29912
      have b0e30266 : y = (k y x) ∨ y = (M.op x y) := by grind
      have b0e30293 : y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e41 y y
           have i₂ := b0e30053
           grind)
        | exact superpose b0e30053 b0e41
        | exact resolve b0e41 b0e30053
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30053
      have b0e30319 : y = (k y x) := by
        first
        | (have j1 := b0e260 y x
           grind)
        | (have r₁ := b0e30266
           have r₂ := b0e260 y x
           grind)
        | exact resolve b0e30266 b0e260
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e260 b0e30266
      have b0e31407 : x ≠ y ∨ x = (M.op x y) := by grind
      clear b0e30293
      have b0e39662 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y X0) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e4759 X0
           have i₂ := b0e2359 x y
           grind)
        | exact superpose b0e2359 b0e4759
        | (have j0 := b0e4759 X0
           have j1 := b0e2359 x y
           grind)
        | (have r₁ := b0e4759 X0
           have r₂ := b0e2359 x y
           grind)
        | exact resolve b0e4759 b0e2359
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2359
      have b0e39668 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
        intro X0
        first
        | (have j0 := b0e39662 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39662
      have b0e41454 : (σ y) = (M.op y (σ x)) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e39668 (σ x)
           grind)
        | exact superpose b0e39668 b0e18
        | exact resolve b0e18 b0e39668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39668
      have b0e42065 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b0e93 (σ x)
           have i₂ := b0e41454
           grind)
        | exact superpose b0e41454 b0e93
        | exact resolve b0e93 b0e41454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41454
      have b0e42701 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e589 X0 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e589
        | exact resolve b0e589 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e589
      have b0e42849 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y X0) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e4759 X0
           have i₂ := b0e42701 x
           grind)
        | exact superpose b0e42701 b0e4759
        | (have j0 := b0e4759 X0
           have j1 := b0e42701 x
           grind)
        | exact resolve b0e4759 b0e42701
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4759 b0e42701
      have b0e42927 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
        intro X0
        first
        | (have j0 := b0e42849 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42849
      have b0e44433 : ∀ X0 : G, (σ x) = (M.op y (σ y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e751 x X0 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e751
        | (have j0 := b0e751 x X0 x
           grind)
        | exact resolve b0e751 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e751
      have b0e45567 : (σ y) = (M.op y (σ x)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e42927 (σ x)
           grind)
        | exact superpose b0e42927 b0e18
        | exact resolve b0e18 b0e42927
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42927
      have b0e45729 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e93 (σ x)
           have i₂ := b0e45567
           grind)
        | exact superpose b0e45567 b0e93
        | exact resolve b0e93 b0e45567
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93 b0e45567
      have b0e48376 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e42065
           grind)
        | exact superpose b0e42065 b0e16
        | exact resolve b0e16 b0e42065
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42065
      have b0e50845 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e45729
           grind)
        | exact superpose b0e45729 b0e16
        | exact resolve b0e16 b0e45729
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45729
      have b0e70573 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X1) = (k (σ X0) (σ X0)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e2756 X0 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e2756
        | (have j0 := b0e2756 X1 (σ X0)
           grind)
        | exact resolve b0e2756 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2756
      have b0e71317 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X1) = (k (σ X0) (σ X0)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e70573 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e70573
        | (have j0 := b0e70573 X0 X1
           grind)
        | exact resolve b0e70573 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70573
      have b0e71320 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e71317 X0 X1
           have i₂ := b0e15 X0 X0
           grind)
        | exact superpose b0e15 b0e71317
        | (have j0 := b0e71317 X0 X1
           grind)
        | exact resolve b0e71317 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71317
      have b0e74075 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e4542 x y
           grind)
        | exact superpose b0e4542 b0e16
        | (have j1 := b0e4542 x y
           grind)
        | (have r₁ := b0e16
           have r₂ := b0e4542 (σ (M.op x y)) (M.op (σ x) (σ y))
           grind)
        | (have r₁ := b0e16
           have r₂ := b0e4542 (M.op (σ x) (σ y)) (σ (M.op x y))
           grind)
        | exact resolve b0e16 b0e4542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4542
      have b0e74615 : (σ x) = (σ (k y y)) ∨ x = y := by
        first
        | (have j1 := b0e71320 y x
           grind)
        | (have r₁ := b0e74075
           have r₂ := b0e71320 y x
           grind)
        | (have r₁ := b0e74075
           have r₂ := b0e71320 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e74075
           have r₂ := b0e71320 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e74075 b0e71320
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71320 b0e74075
      have b0e74688 : (τ (σ x)) = (k y y) ∨ x = y := by
        first
        | (have i₁ := b0e11 (k y y)
           have i₂ := b0e74615
           grind)
        | exact superpose b0e74615 b0e11
        | exact resolve b0e11 b0e74615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74615
      have b0e74784 : x = (k y y) ∨ x = y := by
        first
        | (have i₁ := b0e74688
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e74688
        | exact resolve b0e74688 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74688
      have b0e74922 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = y := by
        first
        | (have i₁ := b0e2606 y y
           have i₂ := b0e74784
           grind)
        | exact superpose b0e74784 b0e2606
        | exact resolve b0e2606 b0e74784
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2606 b0e74784
      have b0e74940 : x = (M.op y y) ∨ x = y := by grind
      clear b0e74922
      have b0e75092 : x = (M.op x y) ∨ x = y := by
        first
        | (have i₁ := b0e41 y y
           have i₂ := b0e74940
           grind)
        | exact superpose b0e74940 b0e41
        | exact resolve b0e41 b0e74940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e74940
      have b0e75112 : x = (M.op x y) := by
        first
        | (have r₁ := b0e75092
           have r₂ := b0e31407
           grind)
        | exact resolve b0e75092 b0e31407
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31407 b0e75092
      have b0e75257 : ∀ X0 : G, (σ x) ≠ (M.op y (σ y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e4706 X0
           have i₂ := b0e75112
           grind)
        | exact superpose b0e75112 b0e4706
        | (have j0 := b0e4706 X0
           grind)
        | exact resolve b0e4706 b0e75112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4706
      have b0e75266 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b0e48376
           have i₂ := b0e75112
           grind)
        | exact superpose b0e75112 b0e48376
        | exact resolve b0e48376 b0e75112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48376
      have b0e75267 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e50845
           have i₂ := b0e75112
           grind)
        | exact superpose b0e75112 b0e50845
        | exact resolve b0e50845 b0e75112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50845
      have b0e75300 : y = (M.op y x) := by grind
      clear b0e75267
      have b0e75301 : x = (M.op y y) := by grind
      clear b0e75266
      have b0e75317 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
        intro X0
        first
        | (have j0 := b0e75257 X0
           have j1 := b0e44433 X0
           grind)
        | (have r₁ := b0e75257 X0
           have r₂ := b0e44433 X0
           grind)
        | exact resolve b0e75257 b0e44433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44433 b0e75257
      have b0e75488 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X1 y X0
           have i₂ := b0e75301
           grind)
        | exact superpose b0e75301 b0e36
        | exact resolve b0e36 b0e75301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e75493 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e161 y X0
           have i₂ := b0e75301
           grind)
        | exact superpose b0e75301 b0e161
        | exact resolve b0e161 b0e75301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e161
      have b0e75506 : ∀ X0 : G, (M.op X0 (M.op y x)) = (k (M.op y x) X0) ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b0e1161 y x
           have i₂ := b0e75301
           grind)
        | exact superpose b0e75301 b0e1161
        | exact resolve b0e1161 b0e75301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1161
      have b0e75547 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b0e75506 X0
           have i₂ := b0e75300
           grind)
        | exact superpose b0e75300 b0e75506
        | (have j0 := b0e75506 X0
           grind)
        | exact resolve b0e75506 b0e75300
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75300 b0e75506
      have b0e90574 : (σ (M.op x y)) ≠ (σ (k y x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e75317 y
           grind)
        | exact superpose b0e75317 b0e16
        | exact resolve b0e16 b0e75317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e90747 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e90574
           have i₂ := b0e30319
           grind)
        | exact superpose b0e30319 b0e90574
        | exact resolve b0e90574 b0e30319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90574
      have b0e90836 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b0e90747
           have i₂ := b0e75112
           grind)
        | exact superpose b0e75112 b0e90747
        | exact resolve b0e90747 b0e75112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75112 b0e90747
      have b0e92418 : (M.op y (σ y)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by
        first
        | (have i₁ := b0e2841 y
           have i₂ := b0e75547 y
           grind)
        | exact superpose b0e75547 b0e2841
        | (have j1 := b0e75547 y
           grind)
        | exact resolve b0e2841 b0e75547
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2841 b0e75547
      have b0e92422 : (σ x) = (M.op y (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by
        first
        | (have i₁ := b0e92418
           have i₂ := b0e75301
           grind)
        | exact superpose b0e75301 b0e92418
        | exact resolve b0e92418 b0e75301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92418
      have b0e92466 : (σ x) = (M.op x (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by
        first
        | (have i₁ := b0e92422
           have i₂ := b0e75493 (σ y)
           grind)
        | exact superpose b0e75493 b0e92422
        | exact resolve b0e92422 b0e75493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75493 b0e92422
      have b0e92492 : (σ x) = (σ y) ∨ (σ x) = (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e92466
           have i₂ := b0e75301
           grind)
        | exact superpose b0e75301 b0e92466
        | exact resolve b0e92466 b0e75301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75301 b0e92466
      have b0e92510 : (σ x) = (M.op x (σ y)) ∨ x = y := by
        first
        | (have r₁ := b0e92492
           have r₂ := b0e90836
           grind)
        | exact resolve b0e92492 b0e90836
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92492
      have b0e97178 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e75488 x (σ y)
           have i₂ := b0e92510
           grind)
        | exact superpose b0e92510 b0e75488
        | exact resolve b0e75488 b0e92510
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75488 b0e92510
      have b0e97180 : (σ x) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e97178
           have i₂ := b0e75317 y
           grind)
        | exact superpose b0e75317 b0e97178
        | exact resolve b0e97178 b0e75317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75317 b0e97178
      have b0e97205 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e97180
           have i₂ := b0e30319
           grind)
        | exact superpose b0e30319 b0e97180
        | exact resolve b0e97180 b0e30319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30319 b0e97180
      have b0e97216 : x = y := by
        first
        | (have r₁ := b0e97205
           have r₂ := b0e90836
           grind)
        | exact resolve b0e97205 b0e90836
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97205
      have b0e97989 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e90836
           have i₂ := b0e97216
           grind)
        | exact superpose b0e97216 b0e90836
        | exact resolve b0e90836 b0e97216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90836 b0e97216
      have b0e97990 : False := by grind
      exact b0e97990
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op x x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : x = (k x y) := by grind
      have b1e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b1e29 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 x X0
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e29 (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)
           have i₂ := b1e10 X0 (M.op (M.op X1 X0) X0) X1
           grind)
        | exact superpose b1e10 b1e29
        | exact resolve b1e29 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29
      have b1e44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e47 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
      have b1e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 X0
           have i₂ := b1e14 (σ X1) (σ X0)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X1) (σ X0)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e83 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e22 X1 X0
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e156 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e44 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44
      have b1e171 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b1e47 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47
      have b1e172 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e171
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e171
        | exact resolve b1e171 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e171
      have b1e173 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e172
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e172
        | exact resolve b1e172 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e172
      have b1e175 : (M.op (σ x) (σ x)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e36 (σ x) (σ y)
           have i₂ := b1e173
           grind)
        | exact superpose b1e173 b1e36
        | exact resolve b1e36 b1e173
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36
      have b1e554 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e48 x x
           grind)
        | exact superpose b1e48 b1e18
        | (have j1 := b1e48 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e48 y x
           grind)
        | exact resolve b1e18 b1e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48
      have b1e617 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e554
           have i₂ := b1e175
           grind)
        | exact superpose b1e175 b1e554
        | exact resolve b1e554 b1e175
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e554
      have b1e681 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b1e83
      have b1e698 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e681 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e681
        | exact resolve b1e681 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e681
      have b1e718 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e156 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e156
        | (have j0 := b1e156 x x
           grind)
        | exact resolve b1e156 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e156
      have b1e1148 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e617
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e617
        | (have j1 := b1e14 x x
           grind)
        | exact resolve b1e617 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e617
      have b1e1150 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1148
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1148
        | exact resolve b1e1148 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1148
      have b1e1151 : (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by grind
      clear b1e1150
      have b1e1160 : (σ x) = (M.op y (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e1151
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1151
        | exact resolve b1e1151 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1151
      have b1e1167 : x = (k x (τ (M.op y (σ x)))) := by
        first
        | (have i₁ := b1e698 x
           have i₂ := b1e175
           grind)
        | exact superpose b1e175 b1e698
        | exact resolve b1e698 b1e175
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e175 b1e698
      have b1e1290 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e1167
           have i₂ := b1e1160
           grind)
        | exact superpose b1e1160 b1e1167
        | exact resolve b1e1167 b1e1160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1160 b1e1167
      have b1e1313 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e1290
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e1290
        | exact resolve b1e1290 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1290
      have b1e1315 : x = (k x x) := by
        first
        | (have r₁ := b1e1313
           have r₂ := b1e718
           grind)
        | exact resolve b1e1313 b1e718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e718 b1e1313
      have b1e1376 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e1315
           grind)
        | exact superpose b1e1315 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e1315
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1315
      have b1e1377 : x = (M.op x x) := by grind
      clear b1e1376
      have b1e1439 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e1377
           grind)
        | exact superpose b1e1377 b1e17
        | exact resolve b1e17 b1e1377
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1377
      have b1e1533 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e173
           have i₂ := b1e1439
           grind)
        | exact superpose b1e1439 b1e173
        | exact resolve b1e173 b1e1439
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e173
      have b1e2428 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e1533
           grind)
        | exact superpose b1e1533 b1e18
        | exact resolve b1e18 b1e1533
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1533
      have b1e2481 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e2428
           have i₂ := b1e1439
           grind)
        | exact superpose b1e1439 b1e2428
        | exact resolve b1e2428 b1e1439
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1439 b1e2428
      have b1e2482 : False := by grind
      exact b1e2482
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op x x) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : (σ x) = (k (σ x) (σ y)) := by grind
      have b2e21 : (σ x) = (σ (k x y)) := by
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
      have b2e26 : (k x y) = (τ (σ x)) := by
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
      have b2e27 : x = (k x y) := by
        first
        | (have i₁ := b2e26
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e26
        | exact resolve b2e26 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26
      have b2e45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 X0
           have i₂ := b2e14 (σ X1) (σ X0)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X1) (σ X0)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e50 : x = (M.op y x) ∨ y = (M.op x x) := by
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
      have b2e53 : x = (M.op y x) := by
        first
        | (have r₁ := b2e50
           have r₂ := b2e17
           grind)
        | exact resolve b2e50 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50
      have b2e584 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e48 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e48
        | exact resolve b2e48 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48
      have b2e1997 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e584
           grind)
        | exact superpose b2e584 b2e11
        | exact resolve b2e11 b2e584
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e584
      have b2e2014 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e1997
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e1997
        | exact resolve b2e1997 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1997
      have b2e2021 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e45 x x
           have i₂ := b2e2014
           grind)
        | exact superpose b2e2014 b2e45
        | exact resolve b2e45 b2e2014
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45 b2e2014
      have b2e2024 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e2021
           have r₂ := b2e17
           grind)
        | exact resolve b2e2021 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2021
      have b2e2108 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e2024
           grind)
        | exact superpose b2e2024 b2e11
        | exact resolve b2e11 b2e2024
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2024
      have b2e2124 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e2108
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e2108
        | exact resolve b2e2108 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2108
      have b2e2125 : x = y := by grind
      clear b2e2124
      have b2e2191 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e2125
           grind)
        | exact superpose b2e2125 b2e16
        | exact resolve b2e16 b2e2125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2197 : x = (M.op x x) := by
        first
        | (have i₁ := b2e53
           have i₂ := b2e2125
           grind)
        | exact superpose b2e2125 b2e53
        | exact resolve b2e53 b2e2125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53
      have b2e2217 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e2191
           have i₂ := b2e2197
           grind)
        | exact superpose b2e2197 b2e2191
        | exact resolve b2e2191 b2e2197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2191 b2e2197
      have b2e2224 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e2217
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e2217
        | exact resolve b2e2217 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2217
      have b2e2227 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e2224
           have i₂ := b2e2125
           grind)
        | exact superpose b2e2125 b2e2224
        | exact resolve b2e2224 b2e2125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2125 b2e2224
      have b2e2228 : False := by grind
      exact b2e2228
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e23 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
           have i₂ := b3e10 X0 (M.op (M.op X2 X0) X0) X2
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k (τ X0) X1)
           have i₂ := b3e20 X0 X1
           grind)
        | exact superpose b3e20 b3e11
        | exact resolve b3e11 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e33 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e34 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X2)) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X2 X1 X2
           have i₂ := b3e14 X2 X0
           grind)
        | (have i₁ := b3e10 X0 X1 X2
           have i₂ := b3e14 X0 (M.op X2 X0)
           grind)
        | exact superpose b3e14 b3e10
        | (have j1 := b3e14 X2 X0
           grind)
        | exact resolve b3e10 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e36 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X1) (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e39 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e21 X0 X1
           have i₂ := b3e14 X1 (τ X0)
           grind)
        | exact superpose b3e14 b3e21
        | (have j1 := b3e14 X1 (τ X0)
           grind)
        | exact resolve b3e21 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X0 (τ X1))
           have i₂ := b3e21 X1 X0
           grind)
        | exact superpose b3e21 b3e11
        | exact resolve b3e11 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e47 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b3e23 (M.op (M.op X2 X0) X0) X3 (M.op x x)
           have i₂ := b3e10 X0 x X2
           grind)
        | exact superpose b3e10 b3e23
        | exact resolve b3e23 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e23 X1 X3 x
           have i₂ := b3e23 X1 X0 x
           grind)
        | (have i₁ := b3e23 X0 X1 X0
           have i₂ := b3e23 X0 X0 x
           grind)
        | exact superpose b3e23 b3e23
        | exact resolve b3e23 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e58 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X1 X2 x
           have i₂ := b3e23 X1 X0 x
           grind)
        | (have i₁ := b3e10 X0 X1 X0
           have i₂ := b3e23 X0 X0 X2
           grind)
        | exact superpose b3e23 b3e10
        | exact resolve b3e10 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e64 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b3e47 X0 X2 x
           have i₂ := b3e10 X0 x X2
           grind)
        | exact superpose b3e10 b3e47
        | exact resolve b3e47 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e47
      have b3e71 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e64 X1 x
           have i₂ := b3e23 X1 X0 x
           grind)
        | (have i₁ := b3e64 X0 X0
           have i₂ := b3e23 X0 X0 x
           grind)
        | exact superpose b3e23 b3e64
        | exact resolve b3e64 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e64
      have b3e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e33 (σ X1) (σ X0)
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e33
        | exact resolve b3e33 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e80 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e21 X0 X1
           have i₂ := b3e33 (τ X0) X1
           grind)
        | exact superpose b3e33 b3e21
        | (have j1 := b3e33 (τ X0) X1
           grind)
        | exact resolve b3e21 b3e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e101 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e28 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e28
        | exact resolve b3e28 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e194 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      have b3e203 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b3e44
      have b3e218 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e203 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e203
        | exact resolve b3e203 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e203
      have b3e330 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e36 X0 X0
           have i₂ := b3e14 (σ X0) X1
           grind)
        | (have i₁ := b3e36 X0 X1
           have i₂ := b3e14 X0 (M.op (σ X0) (σ X1))
           grind)
        | exact superpose b3e14 b3e36
        | (have j1 := b3e14 (σ X1) X0
           grind)
        | exact resolve b3e36 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e357 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 X1
           have i₂ := b3e36 X1 X0
           grind)
        | exact superpose b3e36 b3e11
        | (have j1 := b3e36 X1 X0
           grind)
        | exact resolve b3e11 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e358 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X2
           have i₂ := b3e36 X1 X0
           grind)
        | exact superpose b3e36 b3e15
        | (have j1 := b3e36 X1 X0
           grind)
        | exact resolve b3e15 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e519 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e218 X1
           have i₂ := b3e36 X0 X1
           grind)
        | exact superpose b3e36 b3e218
        | (have j1 := b3e36 X0 X1
           grind)
        | exact resolve b3e218 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36 b3e218
      have b3e540 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e519 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e519
        | (have j0 := b3e519 X0 X1
           grind)
        | exact resolve b3e519 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e519
      have b3e662 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X0 X3)) = X3 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e58 X2 X3 X1
           have i₂ := b3e14 X2 X0
           grind)
        | (have i₁ := b3e58 X0 X1 X2
           have i₂ := b3e14 X0 (M.op X0 X0)
           grind)
        | exact superpose b3e14 b3e58
        | (have j1 := b3e14 X2 X0
           grind)
        | exact resolve b3e58 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1318 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e39 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e39
        | exact resolve b3e39 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39
      have b3e1415 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e1318 X0 X1
           have i₂ := b3e15 X1 X0
           grind)
        | exact superpose b3e15 b3e1318
        | (have j0 := b3e1318 X0 X1
           grind)
        | exact resolve b3e1318 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1318
      have b3e2069 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e80 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e80
        | exact resolve b3e80 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e80
      have b3e2120 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2069 X0 X1
           have i₂ := b3e15 X1 X0
           grind)
        | exact superpose b3e15 b3e2069
        | (have j0 := b3e2069 X0 X1
           grind)
        | exact resolve b3e2069 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2069
      have b3e2791 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e14 (σ X0) X1
           have i₂ := b3e78 X0 X0
           grind)
        | exact superpose b3e78 b3e14
        | (have j0 := b3e14 (σ X0) X1
           have j1 := b3e78 X0 X0
           grind)
        | exact resolve b3e14 b3e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e78
      have b3e3337 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e357 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e357
        | exact resolve b3e357 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e357
      have b3e3389 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e3337 X0 X1
           have i₂ := b3e20 X0 X1
           grind)
        | exact superpose b3e20 b3e3337
        | (have j0 := b3e3337 X0 X1
           grind)
        | exact resolve b3e3337 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3337
      have b3e13382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e194 (σ X1)
           have i₂ := b3e358 X1 X0 X1
           grind)
        | exact superpose b3e358 b3e194
        | (have j0 := b3e194 (σ X1)
           have j1 := b3e358 X1 X0 x
           grind)
        | exact resolve b3e194 b3e358
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e194 b3e358
      have b3e13454 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e13382 X0 X1
           have i₂ := b3e15 X1 X1
           grind)
        | exact superpose b3e15 b3e13382
        | (have j0 := b3e13382 X1 X1
           grind)
        | exact resolve b3e13382 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13382
      have b3e18780 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e540 x y
           grind)
        | exact superpose b3e540 b3e16
        | (have j1 := b3e540 x y
           grind)
        | exact resolve b3e16 b3e540
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e540
      have b3e18880 : y = (k y x) := by
        first
        | (have j1 := b3e2120 x y
           grind)
        | (have r₁ := b3e18780
           have r₂ := b3e2120 x y
           grind)
        | exact resolve b3e18780 b3e2120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2120 b3e18780
      have b3e19669 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e1415 x y
           have i₂ := b3e18880
           grind)
        | exact superpose b3e18880 b3e1415
        | (have j0 := b3e1415 x y
           grind)
        | exact resolve b3e1415 b3e18880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1415
      have b3e91376 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b3e2791 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2791
      have b3e91377 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b3e91376 X0 X1
           have j1 := b3e330 X1 X0
           grind)
        | (have r₁ := b3e91376 (k X1 X1) X0
           have r₂ := b3e330 X0 X1
           grind)
        | (have r₁ := b3e91376 X0 (σ (k X1 X1))
           have r₂ := b3e330 (σ X0) X1
           grind)
        | (have r₁ := b3e91376 X1 X0
           have r₂ := b3e330 X0 X1
           grind)
        | exact resolve b3e91376 b3e330
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e330 b3e91376
      have b3e91416 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e20 X1 (τ X1)
           have i₂ := b3e91377 (τ X1) X0
           grind)
        | (have i₁ := b3e20 X0 X1
           have i₂ := b3e91377 X0 (σ (k (τ X0) X1))
           grind)
        | exact superpose b3e91377 b3e20
        | (have j1 := b3e91377 (τ X1) X0
           grind)
        | exact resolve b3e20 b3e91377
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e91417 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X1 X1)
           have i₂ := b3e91377 X1 X0
           grind)
        | (have i₁ := b3e11 X0
           have i₂ := b3e91377 X0 (σ X0)
           grind)
        | exact superpose b3e91377 b3e11
        | (have j1 := b3e91377 X1 X0
           grind)
        | exact resolve b3e11 b3e91377
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e91377
      have b3e91436 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e91416 X0 X1
           have i₂ := b3e12 X1
           grind)
        | exact superpose b3e12 b3e91416
        | (have j0 := b3e91416 X0 X1
           grind)
        | exact resolve b3e91416 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e91416
      have b3e91442 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e91436 X0 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e91436
        | (have j0 := b3e91436 X0 X1
           grind)
        | exact resolve b3e91436 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e91436
      have b3e91911 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e91417 (σ X0) X1
           grind)
        | exact superpose b3e91417 b3e15
        | (have j1 := b3e91417 (σ X0) X1
           grind)
        | exact resolve b3e15 b3e91417
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e91417
      have b3e91919 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e91911 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e91911
        | (have j0 := b3e91911 X0 X1
           grind)
        | exact resolve b3e91911 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e91911
      have b3e92738 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e91919 x y
           grind)
        | exact superpose b3e91919 b3e16
        | (have j1 := b3e91919 x y
           grind)
        | exact resolve b3e16 b3e91919
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e91919
      have b3e92860 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e92738
           have i₂ := b3e18880
           grind)
        | exact superpose b3e18880 b3e92738
        | exact resolve b3e92738 b3e18880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e18880 b3e92738
      have b3e92913 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e92860
           have i₂ := b3e19669
           grind)
        | exact superpose b3e19669 b3e92860
        | (have r₁ := b3e92860
           have r₂ := b3e19669
           grind)
        | exact resolve b3e92860 b3e19669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19669 b3e92860
      have b3e92915 : x = (k y y) ∨ x = (M.op y y) := by grind
      clear b3e92913
      have b3e93047 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e14 y y
           have i₂ := b3e92915
           grind)
        | exact superpose b3e92915 b3e14
        | (have j0 := b3e14 y x
           grind)
        | exact resolve b3e14 b3e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e93066 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e91442 y y
           have i₂ := b3e92915
           grind)
        | exact superpose b3e92915 b3e91442
        | exact resolve b3e91442 b3e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e91442 b3e92915
      have b3e93071 : x = (M.op y y) ∨ x = y := by grind
      clear b3e93066
      have b3e93080 : y = (M.op y y) ∨ x = (M.op y y) := by grind
      clear b3e93047
      have b3e93857 : x ≠ y ∨ x = (M.op y y) := by grind
      clear b3e93080
      have b3e93870 : x = (M.op y y) := by
        first
        | (have r₁ := b3e93857
           have r₂ := b3e93071
           grind)
        | exact resolve b3e93857 b3e93071
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93071 b3e93857
      have b3e93922 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e10 X1 y X0
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e10
        | exact resolve b3e10 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e93925 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e23 X1 y X0
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e23
        | exact resolve b3e23 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e23
      have b3e93929 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e52 X0 X1 y
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e52
        | exact resolve b3e52 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e52
      have b3e93931 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e58 X0 X1 y
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e58
        | exact resolve b3e58 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e58
      have b3e93932 : ∀ X0 : G, (M.op X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b3e71 y X0
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e71
        | exact resolve b3e71 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e71
      have b3e93971 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e662 X0 y X2 X1
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e662
        | (have j0 := b3e662 X0 X1 X2 x
           grind)
        | exact resolve b3e662 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e662
      have b3e94067 : ∀ X0 : G, y = (M.op (M.op X0 X0) x) ∨ x = (k y y) := by
        intro X0
        first
        | (have i₁ := b3e34 y x y
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e34
        | exact resolve b3e34 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e34
      have b3e94147 : ∀ X1 : G, (M.op x (M.op x X1)) = X1 := by
        intro X1
        first
        | (have i₁ := b3e93922 x X1
           have i₂ := b3e93925 x X1
           grind)
        | exact superpose b3e93925 b3e93922
        | exact resolve b3e93922 b3e93925
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93922
      have b3e109200 : y = (M.op x x) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e93929 x x
           have i₂ := b3e94067 x
           grind)
        | exact superpose b3e94067 b3e93929
        | exact resolve b3e93929 b3e94067
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e94067
      have b3e109276 : x = (k y y) := by
        first
        | (have r₁ := b3e109200
           have r₂ := b3e17
           grind)
        | exact resolve b3e109200 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e109200
      have b3e139759 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e93971 y y X0
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e93971
        | (have j0 := b3e93971 y x X0
           grind)
        | exact resolve b3e93971 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93971
      have b3e139867 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b3e139759 X0
           grind)
        | (have r₁ := b3e139759 X0
           have r₂ := b3e17
           grind)
        | exact resolve b3e139759 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e139759
      have b3e194547 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have j0 := b3e13454 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13454
      have b3e194548 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have j0 := b3e194547 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e194547
      have b3e194549 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have j0 := b3e194548 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e194548
      have b3e194558 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e194549 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e194549
        | exact resolve b3e194549 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e194759 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e93929 (σ X0) X1
           have i₂ := b3e194549 X0
           grind)
        | exact superpose b3e194549 b3e93929
        | exact resolve b3e93929 b3e194549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93929 b3e194549
      have b3e195079 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b3e194558 X0
           have i₂ := b3e21 X0 (τ X0)
           grind)
        | exact superpose b3e21 b3e194558
        | exact resolve b3e194558 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21 b3e194558
      have b3e195123 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b3e195079 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e195079
        | exact resolve b3e195079 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e195079
      have b3e195818 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e101 X0 X0
           have i₂ := b3e195123 (τ X0)
           grind)
        | exact superpose b3e195123 b3e101
        | exact resolve b3e101 b3e195123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e101
      have b3e195884 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e195818 X0
           have i₂ := b3e195123 X0
           grind)
        | exact superpose b3e195123 b3e195818
        | exact resolve b3e195818 b3e195123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e195123 b3e195818
      have b3e196642 : ∀ X0 X1 : G, (M.op x (M.op (τ (M.op X0 X0)) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e93931 (τ X0) X1
           have i₂ := b3e195884 X0
           grind)
        | exact superpose b3e195884 b3e93931
        | exact resolve b3e93931 b3e195884
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93931 b3e195884
      have b3e197698 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e194759 y X0
           have i₂ := b3e109276
           grind)
        | exact superpose b3e109276 b3e194759
        | exact resolve b3e194759 b3e109276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e109276 b3e194759
      have b3e198614 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e197698 (σ y)
           grind)
        | exact superpose b3e197698 b3e16
        | exact resolve b3e16 b3e197698
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e197698
      have b3e204875 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X2)) = X2 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e196642 X1 X2
           have i₂ := b3e3389 X1 X0
           grind)
        | (have i₁ := b3e196642 X0 X1
           have i₂ := b3e3389 X0 (τ (M.op X0 X0))
           grind)
        | exact superpose b3e3389 b3e196642
        | (have j1 := b3e3389 X1 X0
           grind)
        | exact resolve b3e196642 b3e3389
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3389 b3e196642
      have b3e301496 : ∀ X0 : G, y = (M.op x x) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e204875 y X0 y
           have i₂ := b3e93870
           grind)
        | exact superpose b3e93870 b3e204875
        | (have j0 := b3e204875 y X0 x
           grind)
        | exact resolve b3e204875 b3e93870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93870 b3e204875
      have b3e301504 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b3e301496 X0
           grind)
        | (have r₁ := b3e301496 X0
           have r₂ := b3e17
           grind)
        | exact resolve b3e301496 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e301496
      have b3e301516 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b3e28 X0 y
           have i₂ := b3e301504 X0
           grind)
        | exact superpose b3e301504 b3e28
        | exact resolve b3e28 b3e301504
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e28 b3e301504
      have b3e301577 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (M.op y (τ X0)) := by
        intro X0
        first
        | (have i₁ := b3e301516 X0
           have i₂ := b3e139867 (τ X0)
           grind)
        | exact superpose b3e139867 b3e301516
        | exact resolve b3e301516 b3e139867
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e139867 b3e301516
      have b3e302224 : (τ (σ y)) = (M.op y (τ (M.op x (σ y)))) := by
        first
        | (have i₁ := b3e301577 (M.op x (σ y))
           have i₂ := b3e93932 (σ y)
           grind)
        | exact superpose b3e93932 b3e301577
        | exact resolve b3e301577 b3e93932
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93932 b3e301577
      have b3e302407 : y = (M.op y (τ (M.op x (σ y)))) := by
        first
        | (have i₁ := b3e302224
           have i₂ := b3e11 y
           grind)
        | exact superpose b3e11 b3e302224
        | exact resolve b3e302224 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e302224
      have b3e302504 : (M.op y (τ (M.op x (σ y)))) = (M.op x (τ (M.op x (σ y)))) := by
        first
        | (have i₁ := b3e93925 y (τ (M.op x (σ y)))
           have i₂ := b3e302407
           grind)
        | exact superpose b3e302407 b3e93925
        | exact resolve b3e93925 b3e302407
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93925
      have b3e302511 : y = (M.op x (τ (M.op x (σ y)))) := by
        first
        | (have i₁ := b3e302504
           have i₂ := b3e302407
           grind)
        | exact superpose b3e302407 b3e302504
        | exact resolve b3e302504 b3e302407
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e302407 b3e302504
      have b3e302562 : (M.op x y) = (τ (M.op x (σ y))) := by
        first
        | (have i₁ := b3e94147 (τ (M.op x (σ y)))
           have i₂ := b3e302511
           grind)
        | exact superpose b3e302511 b3e94147
        | exact resolve b3e94147 b3e302511
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e94147 b3e302511
      have b3e302763 : (σ (M.op x y)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b3e12 (M.op x (σ y))
           have i₂ := b3e302562
           grind)
        | exact superpose b3e302562 b3e12
        | exact resolve b3e12 b3e302562
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e302562
      have b3e302773 : False := by grind
      exact b3e302773

/-- `Equation1738`: `x = (y ◇ y) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxy_pyx_Equation1738 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1738 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1738.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : x = (M.op x y) := by grind
      have b0e18 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (σ x) ≠ (σ x) := by
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
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : x = (M.op x y) := by grind
      have b1e18 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b1e22 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) := by
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
      have b1e24 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
           have i₂ := b1e10 X0 (M.op (M.op X2 X0) X0) X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e25 : ∀ X0 : G, y = (M.op (M.op X0 X0) x) := by
        intro X0
        first
        | (have i₁ := b1e22 X0
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e22
        | exact resolve b1e22 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e26 : ∀ X0 : G, x = (M.op (M.op X0 X0) y) := by
        intro X0
        first
        | (have i₁ := b1e10 x X0 x
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e10
        | exact resolve b1e10 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e27 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b1e10 x X0 (M.op x x)
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e10
        | exact resolve b1e10 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e28 : x ≠ x ∨ x = (k x y) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : x = (k x y) := by grind
      clear b1e28
      have b1e34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 X0
           have i₂ := b1e14 (σ X1) (σ X0)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X1) (σ X0)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e44 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e20 X0 X1
           grind)
        | exact superpose b1e20 b1e11
        | exact resolve b1e11 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20
      have b1e45 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b1e10 (M.op y x) X0 (M.op y x)
           have i₂ := b1e27 (M.op y x)
           grind)
        | exact superpose b1e27 b1e10
        | exact resolve b1e10 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27
      have b1e48 : y = (M.op y x) := by
        first
        | (have i₁ := b1e45 x
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e45
        | exact resolve b1e45 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e55 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e21 X1 X0
           grind)
        | exact superpose b1e21 b1e11
        | exact resolve b1e11 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e59 : y ≠ y ∨ y = (k y x) := by
        first
        | (have i₁ := b1e13 y x
           have i₂ := b1e48
           grind)
        | exact superpose b1e48 b1e13
        | (have r₁ := b1e13 y x
           have r₂ := b1e48
           grind)
        | exact resolve b1e13 b1e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48
      have b1e61 : y = (k y x) := by grind
      clear b1e59
      have b1e64 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b1e24 (M.op (M.op X2 X0) X0) X3 (M.op x x)
           have i₂ := b1e10 X0 x X2
           grind)
        | exact superpose b1e10 b1e24
        | exact resolve b1e24 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e75 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
        intro X0 X1 X3
        first
        | (have i₁ := b1e24 X1 X3 x
           have i₂ := b1e24 X1 X0 x
           grind)
        | (have i₁ := b1e24 X0 X1 X0
           have i₂ := b1e24 X0 X0 x
           grind)
        | exact superpose b1e24 b1e24
        | exact resolve b1e24 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e76 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e24 X1 x X0
           have i₂ := b1e24 X1 x X2
           grind)
        | (have i₁ := b1e24 X0 X0 X2
           have i₂ := b1e24 X0 X1 X0
           grind)
        | exact superpose b1e24 b1e24
        | exact resolve b1e24 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e82 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X1 X2 x
           have i₂ := b1e24 X1 X0 x
           grind)
        | (have i₁ := b1e10 X0 X1 X0
           have i₂ := b1e24 X0 X0 X2
           grind)
        | exact superpose b1e24 b1e10
        | exact resolve b1e10 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e102 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b1e64 X0 X2 x
           have i₂ := b1e10 X0 x X2
           grind)
        | exact superpose b1e10 b1e64
        | exact resolve b1e64 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e64
      have b1e204 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X0)) = (M.op (M.op X2 X2) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e24 (σ X0) X2 (σ X1)
           have i₂ := b1e34 X1 X0
           grind)
        | exact superpose b1e34 b1e24
        | (have j1 := b1e34 X1 X0
           grind)
        | exact resolve b1e24 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e208 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op X2 X2) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e24 (σ X1) X2 (σ X0)
           have i₂ := b1e34 X1 X0
           grind)
        | exact superpose b1e34 b1e24
        | (have j1 := b1e34 X1 X0
           grind)
        | exact resolve b1e24 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e232 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e102 (σ X0) (σ X1)
           have i₂ := b1e34 X1 X0
           grind)
        | exact superpose b1e34 b1e102
        | (have j1 := b1e34 X1 X0
           grind)
        | exact resolve b1e102 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e241 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e102 X1 x
           have i₂ := b1e24 X1 X0 x
           grind)
        | (have i₁ := b1e102 X0 X0
           have i₂ := b1e24 X0 X0 x
           grind)
        | exact superpose b1e24 b1e102
        | exact resolve b1e102 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e102
      have b1e265 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e44 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e44
        | exact resolve b1e44 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44
      have b1e290 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X1) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e13 X1 (M.op (M.op X0 X0) X1)
           have i₂ := b1e241 X0 X1
           grind)
        | exact superpose b1e241 b1e13
        | (have r₁ := b1e13 X1 (M.op (M.op X0 X0) X1)
           have r₂ := b1e241 X0 X1
           grind)
        | exact resolve b1e13 b1e241
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e241
      have b1e292 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X0)) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e290 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e290
      have b1e372 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e75 X2 X3 (M.op X1 X1)
           have i₂ := b1e75 X1 (M.op X1 X1) X0
           grind)
        | (have i₁ := b1e75 X2 X3 (M.op X1 X1)
           have i₂ := b1e75 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b1e75 b1e75
        | exact resolve b1e75 b1e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e434 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X2 X3) X3)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X3 (M.op X1 X1) X2
           have i₂ := b1e75 X1 (M.op X1 X1) X0
           grind)
        | (have i₁ := b1e10 X3 (M.op X1 X1) X2
           have i₂ := b1e75 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b1e75 b1e10
        | exact resolve b1e10 b1e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e437 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e25 (M.op X1 X1)
           have i₂ := b1e75 X1 (M.op X1 X1) X0
           grind)
        | (have i₁ := b1e25 (M.op X1 X1)
           have i₂ := b1e75 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b1e75 b1e25
        | exact resolve b1e25 b1e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25
      have b1e475 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 X1) (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e55 X0 (M.op (M.op X1 X1) (σ X0))
           have i₂ := b1e292 (σ X0) X1
           grind)
        | exact superpose b1e292 b1e55
        | exact resolve b1e55 b1e292
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55 b1e292
      have b1e478 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 X1) (σ X0)))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e475 X0 X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e475
        | exact resolve b1e475 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e475
      have b1e529 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X0)) = (M.op (M.op X2 (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e76 X2 (σ X0) (σ X1)
           have i₂ := b1e34 X1 X0
           grind)
        | exact superpose b1e34 b1e76
        | (have j1 := b1e34 X1 X0
           grind)
        | exact resolve b1e76 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e722 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X1)) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e437 (M.op X1 X1) X1
           have i₂ := b1e76 (M.op X1 X1) (M.op X1 X1) X0
           grind)
        | (have i₁ := b1e437 (M.op X1 X1) X1
           have i₂ := b1e76 X0 (M.op X1 X1) (M.op X1 X1)
           grind)
        | exact superpose b1e76 b1e437
        | exact resolve b1e437 b1e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e76 b1e437
      have b1e2920 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e204 x y X0
           have i₂ := b1e31
           grind)
        | exact superpose b1e31 b1e204
        | (have j0 := b1e204 x y x
           grind)
        | exact resolve b1e204 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31 b1e204
      have b1e3024 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ x) (σ x)) := by
        intro X0
        first
        | (have j0 := b1e2920 X0
           grind)
        | (have r₁ := b1e2920 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e2920 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2920
      have b1e3066 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) := by
        intro X0
        first
        | (have i₁ := b1e82 x (σ x) X0
           have i₂ := b1e3024 x
           grind)
        | exact superpose b1e3024 b1e82
        | exact resolve b1e82 b1e3024
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e82 b1e3024
      have b1e3264 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op X0 X0) (σ X1)) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e34 X1 X2
           have i₂ := b1e208 X2 X1 X0
           grind)
        | exact superpose b1e208 b1e34
        | (have j0 := b1e34 X1 X2
           have j1 := b1e208 X2 X1 X2
           grind)
        | exact resolve b1e34 b1e208
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34
      have b1e3308 : ∀ X0 X1 X2 : G, (σ X2) ≠ (M.op (M.op X0 X0) (σ X1)) ∨ (M.op (M.op X0 X0) (σ X1)) = (k (σ X2) (σ X1)) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 (σ X0) (σ X1)
           have i₂ := b1e208 X0 X1 X2
           grind)
        | exact superpose b1e208 b1e13
        | (have j1 := b1e208 X2 X1 X2
           grind)
        | (have r₁ := b1e13 (M.op (σ X1) (σ X1)) (σ X1)
           have r₂ := b1e208 X1 X1 (σ X1)
           grind)
        | exact resolve b1e13 b1e208
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e3425 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op (M.op X1 X1) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e208 X0 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e208
      have b1e3427 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op X0 X0) (σ X1)) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e3264 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3264
      have b1e3440 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k X2 X1)) ∨ (σ X2) ≠ (M.op (M.op X0 X0) (σ X1)) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e3308 X0 X1 X2
           have i₂ := b1e15 X2 X1
           grind)
        | exact superpose b1e15 b1e3308
        | (have j0 := b1e3308 X0 X1 X2
           grind)
        | exact resolve b1e3308 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3308
      have b1e3458 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k X2 X1)) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e3440 X0 X1 X2
           have j1 := b1e3427 X0 X1 (k X2 X1)
           grind)
        | (have r₁ := b1e3440 X0 X1 X2
           have r₂ := b1e3427 X0 X1 X2
           grind)
        | exact resolve b1e3440 b1e3427
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3427 b1e3440
      have b1e3992 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (σ x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e24 X1 (M.op (σ x) (σ x)) X0
           have i₂ := b1e3066 (σ x)
           grind)
        | exact superpose b1e3066 b1e24
        | exact resolve b1e24 b1e3066
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e4001 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e75 X0 X1 (M.op (σ x) (σ x))
           have i₂ := b1e3066 (σ x)
           grind)
        | exact superpose b1e3066 b1e75
        | exact resolve b1e75 b1e3066
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e75
      have b1e4023 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e478 X0 (M.op (σ x) (σ x))
           have i₂ := b1e3066 (σ x)
           grind)
        | exact superpose b1e3066 b1e478
        | exact resolve b1e478 b1e3066
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e478 b1e3066
      have b1e5325 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ x) (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e4001 (M.op X0 X0) X1
           have i₂ := b1e4001 X0 (M.op X0 X0)
           grind)
        | exact superpose b1e4001 b1e4001
        | exact resolve b1e4001 b1e4001
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e42564 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ (k X0 X1))) (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e232 (τ X0) (τ X1)
           have i₂ := b1e265 X1 X0
           grind)
        | exact superpose b1e265 b1e232
        | (have j0 := b1e232 (τ X0) (τ X1)
           grind)
        | exact resolve b1e232 b1e265
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e232 b1e265
      have b1e42725 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (τ (k X0 X1))) X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e42564 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e42564
        | (have j0 := b1e42564 X0 X1
           grind)
        | exact resolve b1e42564 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42564
      have b1e42770 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X1) X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e42725 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e42725
        | (have j0 := b1e42725 X0 X1
           grind)
        | exact resolve b1e42725 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42725
      have b1e42791 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 (M.op (k X0 X1) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e42770 X0 X1
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e42770
        | (have j0 := b1e42770 X0 X1
           grind)
        | exact resolve b1e42770 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42770
      have b1e42800 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X1) X0)) = X0 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e42791 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e42791
        | (have j0 := b1e42791 X0 X1
           grind)
        | exact resolve b1e42791 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42791
      have b1e48986 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) ≠ (σ (k X1 X1)) ∨ (M.op (σ X1) (σ X1)) = (σ (k X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e3425 X1 (M.op x x)
           have i₂ := b1e372 x x X0 (σ X1)
           grind)
        | (have i₁ := b1e3425 X0 x
           have i₂ := b1e372 X0 X1 x (σ X0)
           grind)
        | exact superpose b1e372 b1e3425
        | (have j0 := b1e3425 X1 X0
           grind)
        | exact resolve b1e3425 b1e372
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e372 b1e3425
      have b1e48989 : ∀ X1 : G, (M.op (σ X1) (σ X1)) = (σ (k X1 X1)) := by
        intro X1
        first
        | (have j0 := b1e48986 x X1
           have j1 := b1e3458 x X1 X1
           grind)
        | (have r₁ := b1e48986 x x
           have r₂ := b1e3458 x x x
           grind)
        | exact resolve b1e48986 b1e3458
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3458 b1e48986
      have b1e49205 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e48989 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e48989
        | exact resolve b1e48989 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e49240 : x = (k x (τ (σ (k x x)))) := by
        first
        | (have i₁ := b1e4023 x
           have i₂ := b1e48989 x
           grind)
        | exact superpose b1e48989 b1e4023
        | exact resolve b1e4023 b1e48989
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4023
      have b1e49533 : x = (k x (k x x)) := by
        first
        | (have i₁ := b1e49240
           have i₂ := b1e11 (k x x)
           grind)
        | exact superpose b1e11 b1e49240
        | exact resolve b1e49240 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49240
      have b1e49549 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b1e49205 X0
           have i₂ := b1e21 X0 (τ X0)
           grind)
        | exact superpose b1e21 b1e49205
        | exact resolve b1e49205 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e49205
      have b1e49596 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b1e49549 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e49549
        | exact resolve b1e49549 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49549
      have b1e51987 : x = (M.op x (M.op x x)) ∨ x = (M.op x (k x x)) := by
        first
        | (have i₁ := b1e42800 x (k x x)
           have i₂ := b1e49533
           grind)
        | exact superpose b1e49533 b1e42800
        | (have j0 := b1e42800 x (M.op x x)
           grind)
        | exact resolve b1e42800 b1e49533
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42800 b1e49533
      have b1e51990 : x = (M.op x (M.op x x)) ∨ x = (M.op x (M.op x x)) := by
        first
        | (have i₁ := b1e51987
           have i₂ := b1e49596 x
           grind)
        | exact superpose b1e49596 b1e51987
        | exact resolve b1e51987 b1e49596
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51987
      have b1e51991 : x = (M.op x (M.op x x)) := by grind
      clear b1e51990
      have b1e52572 : y = (M.op (M.op x (M.op x x)) x) := by
        first
        | (have i₁ := b1e722 x x
           have i₂ := b1e51991
           grind)
        | exact superpose b1e51991 b1e722
        | exact resolve b1e722 b1e51991
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e722
      have b1e52623 : y = (M.op x x) := by
        first
        | (have i₁ := b1e52572
           have i₂ := b1e51991
           grind)
        | exact superpose b1e51991 b1e52572
        | exact resolve b1e52572 b1e51991
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51991 b1e52572
      have b1e53066 : x = (M.op y y) := by
        first
        | (have i₁ := b1e26 x
           have i₂ := b1e52623
           grind)
        | exact superpose b1e52623 b1e26
        | exact resolve b1e26 b1e52623
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26 b1e52623
      have b1e61514 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e529 y x X0
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e529
        | (have j0 := b1e529 y x x
           grind)
        | exact resolve b1e529 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e61 b1e529
      have b1e62019 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e61514 x
           have i₂ := b1e3992 x (σ y)
           grind)
        | exact superpose b1e3992 b1e61514
        | exact resolve b1e61514 b1e3992
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3992 b1e61514
      have b1e62149 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e62019
           have i₂ := b1e48989 y
           grind)
        | exact superpose b1e48989 b1e62019
        | exact resolve b1e62019 b1e48989
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48989 b1e62019
      have b1e62253 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e62149
           have i₂ := b1e49596 y
           grind)
        | exact superpose b1e49596 b1e62149
        | exact resolve b1e62149 b1e49596
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49596 b1e62149
      have b1e62340 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e62253
           have i₂ := b1e53066
           grind)
        | exact superpose b1e53066 b1e62253
        | exact resolve b1e62253 b1e53066
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53066 b1e62253
      have b1e62409 : (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have r₁ := b1e62340
           have r₂ := b1e18
           grind)
        | exact resolve b1e62340 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62340
      have b1e62644 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (σ y) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b1e434 X0 X1 (σ y) (σ x)
           have i₂ := b1e62409
           grind)
        | exact superpose b1e62409 b1e434
        | exact resolve b1e434 b1e62409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e434
      have b1e62668 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e62644 X0 X1
           have i₂ := b1e62409
           grind)
        | exact superpose b1e62409 b1e62644
        | exact resolve b1e62644 b1e62409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62409 b1e62644
      have b1e62710 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (M.op X1 X1)) (σ y)) := by
        intro X1
        first
        | (have i₁ := b1e62668 x X1
           have i₂ := b1e4001 x (M.op X1 X1)
           grind)
        | exact superpose b1e4001 b1e62668
        | exact resolve b1e62668 b1e4001
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4001 b1e62668
      have b1e62743 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e62710 x
           have i₂ := b1e5325 x (σ y)
           grind)
        | exact superpose b1e5325 b1e62710
        | exact resolve b1e62710 b1e5325
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5325 b1e62710
      have b1e62769 : False := by grind
      exact b1e62769
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : x ≠ (M.op x y) := by grind
      have b2e18 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e16
        | exact resolve b2e16 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e26 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) := by
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
      have b2e28 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
           have i₂ := b2e10 X0 (M.op (M.op X2 X0) X0) X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e29 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e26 X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e26
        | exact resolve b2e26 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26
      have b2e30 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) X0 (σ x)
           have i₂ := b2e29 (σ x)
           grind)
        | exact superpose b2e29 b2e10
        | exact resolve b2e10 b2e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e32 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e35 : (σ x) = (k (σ x) (σ y)) := by grind
      clear b2e32
      have b2e36 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e35
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e35
        | exact resolve b2e35 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35
      have b2e39 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e36
           grind)
        | exact superpose b2e36 b2e11
        | exact resolve b2e11 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e36
      have b2e40 : x = (k x y) := by
        first
        | (have i₁ := b2e39
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e39
        | exact resolve b2e39 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e39
      have b2e44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 X0
           have i₂ := b2e14 (σ X1) (σ X0)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X1) (σ X0)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e49 : x = (M.op y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e40
           grind)
        | exact superpose b2e40 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40
      have b2e50 : x = (M.op y x) := by
        first
        | (have r₁ := b2e49
           have r₂ := b2e17
           grind)
        | exact resolve b2e49 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e62 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e10 x X0 y
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e10
        | exact resolve b2e10 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e64 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b2e28 (M.op (M.op X2 X0) X0) X3 (M.op x x)
           have i₂ := b2e10 X0 x X2
           grind)
        | exact superpose b2e10 b2e28
        | exact resolve b2e28 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e65 : ∀ X1 : G, (M.op (M.op X1 X1) (σ x)) = (M.op (σ y) (σ x)) := by
        intro X1
        first
        | (have i₁ := b2e28 (σ x) X1 (M.op x x)
           have i₂ := b2e29 x
           grind)
        | exact superpose b2e29 b2e28
        | exact resolve b2e28 b2e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e87 : (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e65 x
           have i₂ := b2e29 x
           grind)
        | exact superpose b2e29 b2e65
        | exact resolve b2e65 b2e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e29 b2e65
      have b2e88 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b2e64 X0 X2 x
           have i₂ := b2e10 X0 x X2
           grind)
        | exact superpose b2e10 b2e64
        | exact resolve b2e64 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e64
      have b2e98 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ y) (σ x)
           have i₂ := b2e87
           grind)
        | exact superpose b2e87 b2e13
        | (have r₁ := b2e13 (σ y) (σ x)
           have r₂ := b2e87
           grind)
        | exact resolve b2e13 b2e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e87
      have b2e100 : (σ y) = (k (σ y) (σ x)) := by grind
      clear b2e98
      have b2e101 : (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b2e100
           have i₂ := b2e15 y x
           grind)
        | exact superpose b2e15 b2e100
        | exact resolve b2e100 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e100
      have b2e143 : (k y x) = (τ (σ y)) := by
        first
        | (have i₁ := b2e11 (k y x)
           have i₂ := b2e101
           grind)
        | exact superpose b2e101 b2e11
        | exact resolve b2e11 b2e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e101
      have b2e144 : y = (k y x) := by
        first
        | (have i₁ := b2e143
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e143
        | exact resolve b2e143 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e143
      have b2e189 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b2e44 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44
      have b2e211 : y = (M.op x y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b2e14 y x
           have i₂ := b2e144
           grind)
        | exact superpose b2e144 b2e14
        | (have j0 := b2e14 y x
           grind)
        | exact resolve b2e14 b2e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e144
      have b2e212 : y = (M.op x y) ∨ x = y := by
        first
        | (have i₁ := b2e211
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e211
        | exact resolve b2e211 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e211
      have b2e245 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e88 X1 x
           have i₂ := b2e28 X1 X0 x
           grind)
        | (have i₁ := b2e88 X0 X0
           have i₂ := b2e28 X0 X0 x
           grind)
        | exact superpose b2e28 b2e88
        | exact resolve b2e88 b2e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28 b2e88
      have b2e305 : (σ x) ≠ (σ y) ∨ x = y := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e212
           grind)
        | exact superpose b2e212 b2e19
        | exact resolve b2e19 b2e212
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e718 : ∀ X0 : G, (M.op X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e245 (M.op x x) X0
           have i₂ := b2e62 x
           grind)
        | exact superpose b2e62 b2e245
        | exact resolve b2e245 b2e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e62 b2e245
      have b2e917 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e13 X0 (M.op x X0)
           have i₂ := b2e718 X0
           grind)
        | exact superpose b2e718 b2e13
        | (have r₁ := b2e13 X0 (M.op x X0)
           have r₂ := b2e718 X0
           grind)
        | exact resolve b2e13 b2e718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e718
      have b2e928 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have j0 := b2e917 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e917
      have b2e1014 : y = (k y y) ∨ x = y := by
        first
        | (have i₁ := b2e928 y
           have i₂ := b2e212
           grind)
        | exact superpose b2e212 b2e928
        | exact resolve b2e928 b2e212
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e212 b2e928
      have b2e1243 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b2e189 y
           have i₂ := b2e1014
           grind)
        | exact superpose b2e1014 b2e189
        | (have j0 := b2e189 y
           grind)
        | exact resolve b2e189 b2e1014
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e189 b2e1014
      have b2e1246 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
      clear b2e1243
      have b2e6928 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b2e30 (σ y)
           have i₂ := b2e1246
           grind)
        | exact superpose b2e1246 b2e30
        | exact resolve b2e30 b2e1246
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30
      have b2e10519 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
        first
        | (have i₁ := b2e1246
           have i₂ := b2e6928
           grind)
        | exact superpose b2e6928 b2e1246
        | exact resolve b2e1246 b2e6928
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1246 b2e6928
      have b2e10592 : (σ x) = (σ y) ∨ x = y := by grind
      clear b2e10519
      have b2e10634 : x = y := by
        first
        | (have r₁ := b2e10592
           have r₂ := b2e305
           grind)
        | exact resolve b2e10592 b2e305
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e305 b2e10592
      have b2e10718 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e10634
           grind)
        | exact superpose b2e10634 b2e19
        | exact resolve b2e19 b2e10634
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e10724 : x = (M.op x x) := by
        first
        | (have i₁ := b2e50
           have i₂ := b2e10634
           grind)
        | exact superpose b2e10634 b2e50
        | exact resolve b2e50 b2e10634
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50 b2e10634
      have b2e10738 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e10718
           have i₂ := b2e10724
           grind)
        | exact superpose b2e10724 b2e10718
        | exact resolve b2e10718 b2e10724
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e10718 b2e10724
      have b2e10739 : False := by grind
      exact b2e10739
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : x ≠ (M.op x y) := by grind
      have b3e18 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e26 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
           have i₂ := b3e10 X0 (M.op (M.op X2 X0) X0) X2
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X1) (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e20 X0 X1
           have i₂ := b3e14 X1 (τ X0)
           grind)
        | exact superpose b3e14 b3e20
        | (have j1 := b3e14 X1 (τ X0)
           grind)
        | exact resolve b3e20 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e62 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b3e26 (M.op (M.op X2 X0) X0) X3 (M.op x x)
           have i₂ := b3e10 X0 x X2
           grind)
        | exact superpose b3e10 b3e26
        | exact resolve b3e26 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26
      have b3e79 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b3e62 X0 X2 x
           have i₂ := b3e10 X0 x X2
           grind)
        | exact superpose b3e10 b3e62
        | exact resolve b3e62 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e62
      have b3e181 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e45 X0 X1
           have i₂ := b3e45 X1 X0
           grind)
        | exact superpose b3e45 b3e45
        | (have j0 := b3e45 X0 X1
           have j1 := b3e45 X0 X1
           grind)
        | exact resolve b3e45 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e45
      have b3e856 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e47 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e47
        | exact resolve b3e47 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e47
      have b3e887 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e856 X0 X1
           have i₂ := b3e15 X1 X0
           grind)
        | exact superpose b3e15 b3e856
        | (have j0 := b3e856 X0 X1
           grind)
        | exact resolve b3e856 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e856
      have b3e3545 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e181 x y
           grind)
        | exact superpose b3e181 b3e16
        | (have j1 := b3e181 x y
           grind)
        | exact resolve b3e16 b3e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e181
      have b3e3608 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
        first
        | (have r₁ := b3e3545
           have r₂ := b3e18
           grind)
        | exact resolve b3e3545 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3545
      have b3e6580 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e3608
           have i₂ := b3e887 x y
           grind)
        | exact superpose b3e887 b3e3608
        | (have j1 := b3e887 x y
           grind)
        | (have r₁ := b3e3608
           have r₂ := b3e887 x y
           grind)
        | exact resolve b3e3608 b3e887
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e887 b3e3608
      have b3e6581 : (σ y) = (σ (k x y)) ∨ y = (M.op y x) := by grind
      clear b3e6580
      have b3e6592 : (k x y) = (τ (σ y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e11 (k x y)
           have i₂ := b3e6581
           grind)
        | exact superpose b3e6581 b3e11
        | exact resolve b3e11 b3e6581
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e6581
      have b3e6652 : y = (k x y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e6592
           have i₂ := b3e11 y
           grind)
        | exact superpose b3e11 b3e6592
        | exact resolve b3e6592 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e6592
      have b3e6745 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e14 x y
           have i₂ := b3e6652
           grind)
        | exact superpose b3e6652 b3e14
        | (have j0 := b3e14 y x
           grind)
        | exact resolve b3e14 b3e6652
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e6652
      have b3e6754 : y = (M.op y x) ∨ x = (M.op x y) := by grind
      clear b3e6745
      have b3e6758 : y = (M.op y x) := by
        first
        | (have r₁ := b3e6754
           have r₂ := b3e17
           grind)
        | exact resolve b3e6754 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e6754
      have b3e6990 : x = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b3e79 x y
           have i₂ := b3e6758
           grind)
        | exact superpose b3e6758 b3e79
        | exact resolve b3e79 b3e6758
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e79
      have b3e7007 : x = (M.op x y) := by
        first
        | (have i₁ := b3e6990
           have i₂ := b3e6758
           grind)
        | exact superpose b3e6758 b3e6990
        | exact resolve b3e6990 b3e6758
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e6758 b3e6990
      have b3e7017 : False := by grind
      exact b3e7017

/-- `Equation1738`: `x = (y ◇ y) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_pxy_pyx_Equation1738 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1738 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1738.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y x) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e33 : y ≠ y ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e13 x y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e13
        | (have j0 := b0e13 x y
           grind)
        | (have r₁ := b0e13 x y
           have r₂ := b0e17
           grind)
        | exact resolve b0e13 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e13 (σ x) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e13
        | (have j0 := b0e13 (σ x) (σ y)
           grind)
        | (have r₁ := b0e13 (σ x) (σ y)
           have r₂ := b0e18
           grind)
        | exact resolve b0e13 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e34
      have b0e38 : (M.op x y) = (k x y) := by grind
      clear b0e33
      have b0e39 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e37
           have i₂ := b0e15 x y
           grind)
        | exact superpose b0e15 b0e37
        | exact resolve b0e37 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e40 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e39
        | exact resolve b0e39 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e39
      have b0e41 : False := by grind
      exact b0e41
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op y x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b1e24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e19 X0 X1
           grind)
        | exact superpose b1e19 b1e11
        | exact resolve b1e11 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19
      have b1e25 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b1e10 x X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e27 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
           have i₂ := b1e10 X0 (M.op (M.op X2 X0) X0) X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e28 : ∀ X0 : G, x = (M.op (M.op X0 X0) y) := by
        intro X0
        first
        | (have i₁ := b1e25 X0
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e25
        | exact resolve b1e25 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25
      have b1e29 : ∀ X0 : G, y = (M.op (M.op X0 X0) x) := by
        intro X0
        first
        | (have i₁ := b1e10 y X0 y
           have i₂ := b1e28 y
           grind)
        | exact superpose b1e28 b1e10
        | exact resolve b1e10 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b1e10 y X0 (M.op x x)
           have i₂ := b1e28 x
           grind)
        | exact superpose b1e28 b1e10
        | exact resolve b1e10 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : y ≠ y ∨ (M.op x y) = (k x y) := by
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
      have b1e34 : (M.op x y) = (k x y) := by grind
      clear b1e31
      have b1e37 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 X0
           have i₂ := b1e14 (σ X1) (σ X0)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X1) (σ X0)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e20 X1 X0
           grind)
        | exact superpose b1e20 b1e11
        | exact resolve b1e11 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20
      have b1e53 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) y) := by
        intro X0
        first
        | (have i₁ := b1e10 (M.op x y) X0 (M.op x y)
           have i₂ := b1e30 (M.op x y)
           grind)
        | exact superpose b1e30 b1e10
        | exact resolve b1e10 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30
      have b1e56 : x = (M.op x y) := by
        first
        | (have i₁ := b1e53 x
           have i₂ := b1e28 x
           grind)
        | exact superpose b1e28 b1e53
        | exact resolve b1e53 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53
      have b1e59 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b1e27 (M.op (M.op X2 X0) X0) X3 (M.op x x)
           have i₂ := b1e10 X0 x X2
           grind)
        | exact superpose b1e10 b1e27
        | exact resolve b1e27 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e69 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
        intro X0 X1 X3
        first
        | (have i₁ := b1e27 X1 X3 x
           have i₂ := b1e27 X1 X0 x
           grind)
        | (have i₁ := b1e27 X0 X1 X0
           have i₂ := b1e27 X0 X0 x
           grind)
        | exact superpose b1e27 b1e27
        | exact resolve b1e27 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e81 : ∀ X0 X1 X2 : G, (M.op X2 X1) ≠ (M.op (M.op X0 X0) X1) ∨ (k X1 (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X1 (M.op X2 X1)
           have i₂ := b1e27 X1 X0 X2
           grind)
        | (have i₁ := b1e13 X0 (M.op X1 X1)
           have i₂ := b1e27 X0 X1 X2
           grind)
        | exact superpose b1e27 b1e13
        | (have j0 := b1e13 X1 (M.op X2 X1)
           grind)
        | (have r₁ := b1e13 X0 (M.op (M.op X1 X1) X0)
           have r₂ := b1e27 X0 X1 (M.op X1 X1)
           grind)
        | exact resolve b1e13 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e95 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b1e59 X0 X2 x
           have i₂ := b1e10 X0 x X2
           grind)
        | exact superpose b1e10 b1e59
        | exact resolve b1e59 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59
      have b1e100 : x ≠ x ∨ (M.op y x) = (k y x) := by
        first
        | (have i₁ := b1e13 y x
           have i₂ := b1e56
           grind)
        | exact superpose b1e56 b1e13
        | (have j0 := b1e13 y x
           grind)
        | (have r₁ := b1e13 y x
           have r₂ := b1e56
           grind)
        | exact resolve b1e13 b1e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e102 : (M.op y x) = (k y x) := by grind
      clear b1e100
      have b1e103 : y = (k y x) := by
        first
        | (have i₁ := b1e102
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e102
        | exact resolve b1e102 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e102
      have b1e162 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X0) (σ X1)
           have i₂ := b1e37 X1 X0
           grind)
        | exact superpose b1e37 b1e13
        | (have j0 := b1e13 (σ X0) (σ X1)
           have j1 := b1e37 X1 X0
           grind)
        | (have r₁ := b1e13 (σ X1) (σ X0)
           have r₂ := b1e37 X0 X1
           grind)
        | exact resolve b1e13 b1e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e163 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 X2) (M.op (σ (k X0 X1)) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (σ X0) X2 (σ X1)
           have i₂ := b1e37 X1 X0
           grind)
        | exact superpose b1e37 b1e10
        | (have j1 := b1e37 X1 X0
           grind)
        | exact resolve b1e10 b1e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e164 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e37 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e165 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e162 X0 X1
           have j1 := b1e13 (σ X0) (σ X1)
           grind)
        | (have r₁ := b1e162 X0 X1
           have r₂ := b1e13 (σ X0) (σ X1)
           grind)
        | exact resolve b1e162 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e162
      have b1e171 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e165 X0 X1
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e165
        | (have j0 := b1e165 X0 X1
           grind)
        | exact resolve b1e165 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e165
      have b1e229 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e95 X1 x
           have i₂ := b1e27 X1 X0 x
           grind)
        | (have i₁ := b1e95 X0 X0
           have i₂ := b1e27 X0 X0 x
           grind)
        | exact superpose b1e27 b1e95
        | exact resolve b1e95 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27 b1e95
      have b1e277 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e24 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e24
        | exact resolve b1e24 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e379 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e29 (M.op X1 X1)
           have i₂ := b1e69 X1 (M.op X1 X1) X0
           grind)
        | (have i₁ := b1e29 (M.op X1 X1)
           have i₂ := b1e69 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b1e69 b1e29
        | exact resolve b1e29 b1e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29 b1e69
      have b1e1101 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e164 y x
           have i₂ := b1e34
           grind)
        | exact superpose b1e34 b1e164
        | (have j0 := b1e164 y x
           grind)
        | exact resolve b1e164 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34 b1e164
      have b1e1107 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have r₁ := b1e1101
           have r₂ := b1e18
           grind)
        | exact resolve b1e1101 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1101
      have b1e1110 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e1107
           have i₂ := b1e56
           grind)
        | exact superpose b1e56 b1e1107
        | exact resolve b1e1107 b1e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e56 b1e1107
      have b1e1397 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e171 (τ X1) (τ X0)
           have i₂ := b1e277 X0 X1
           grind)
        | exact superpose b1e277 b1e171
        | exact resolve b1e171 b1e277
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e171 b1e277
      have b1e1408 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e1397 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e1397
        | (have j0 := b1e1397 X0 X1
           grind)
        | exact resolve b1e1397 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1397
      have b1e1411 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e1408 X0 X1
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e1408
        | (have j0 := b1e1408 X0 X1
           grind)
        | exact resolve b1e1408 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1408
      have b1e1412 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e1411 X0 X1
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e1411
        | (have j0 := b1e1411 X0 X1
           grind)
        | exact resolve b1e1411 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1411
      have b1e1413 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e1412 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e1412
        | (have j0 := b1e1412 X0 X1
           grind)
        | exact resolve b1e1412 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1412
      have b1e1414 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e1413 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e1413
        | (have j0 := b1e1413 X0 X1
           grind)
        | exact resolve b1e1413 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1413
      have b1e1476 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (k X0 (M.op (M.op X1 X1) X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e81 X0 X0 (M.op X1 X1)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e81
      have b1e1477 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e1476 X0 X1
           have i₂ := b1e229 X1 X0
           grind)
        | exact superpose b1e229 b1e1476
        | exact resolve b1e1476 b1e229
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1476
      have b1e1535 : x = (k x y) := by
        first
        | (have i₁ := b1e1477 x (M.op x x)
           have i₂ := b1e379 x x
           grind)
        | exact superpose b1e379 b1e1477
        | exact resolve b1e1477 b1e379
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e379
      have b1e1549 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 X1) (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e50 X0 (M.op (M.op X1 X1) (σ X0))
           have i₂ := b1e1477 (σ X0) X1
           grind)
        | exact superpose b1e1477 b1e50
        | exact resolve b1e50 b1e1477
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50 b1e1477
      have b1e1552 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 X1) (σ X0)))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e1549 X0 X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e1549
        | exact resolve b1e1549 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1549
      have b1e2260 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e163 x y X0
           have i₂ := b1e1535
           grind)
        | exact superpose b1e1535 b1e163
        | (have j0 := b1e163 x y x
           grind)
        | exact resolve b1e163 b1e1535
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e163 b1e1535
      have b1e2322 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) := by
        intro X0
        first
        | (have j0 := b1e2260 X0
           grind)
        | (have r₁ := b1e2260 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e2260 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2260
      have b1e3358 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e229 (M.op (σ x) (σ x)) X0
           have i₂ := b1e2322 (σ x)
           grind)
        | exact superpose b1e2322 b1e229
        | exact resolve b1e229 b1e2322
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e229
      have b1e3369 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e1552 X0 (M.op (σ x) (σ x))
           have i₂ := b1e2322 (σ x)
           grind)
        | exact superpose b1e2322 b1e1552
        | exact resolve b1e1552 b1e2322
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1552 b1e2322
      have b1e6926 : ∀ X0 : G, (k X0 (τ (σ (k X0 x)))) = X0 ∨ (σ x) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e3369 X0
           have i₂ := b1e37 x X0
           grind)
        | exact superpose b1e37 b1e3369
        | (have j1 := b1e37 x X0
           grind)
        | exact resolve b1e3369 b1e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37 b1e3369
      have b1e6977 : ∀ X0 : G, (k X0 (k X0 x)) = X0 ∨ (σ x) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e6926 X0
           have i₂ := b1e11 (k X0 x)
           grind)
        | exact superpose b1e11 b1e6926
        | (have j0 := b1e6926 X0
           grind)
        | exact resolve b1e6926 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6926
      have b1e24982 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
        first
        | (have i₁ := b1e6977 y
           have i₂ := b1e103
           grind)
        | exact superpose b1e103 b1e6977
        | (have j0 := b1e6977 y
           grind)
        | exact resolve b1e6977 b1e103
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e103 b1e6977
      have b1e25230 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y y) := by
        first
        | (have i₁ := b1e3358 (σ y)
           have i₂ := b1e24982
           grind)
        | exact superpose b1e24982 b1e3358
        | exact resolve b1e3358 b1e24982
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3358 b1e24982
      have b1e25267 : y = (k y y) := by
        first
        | (have r₁ := b1e25230
           have r₂ := b1e18
           grind)
        | exact resolve b1e25230 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25230
      have b1e26090 : y ≠ y ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e1414 y y
           have i₂ := b1e25267
           grind)
        | exact superpose b1e25267 b1e1414
        | (have r₁ := b1e1414 y y
           have r₂ := b1e25267
           grind)
        | exact resolve b1e1414 b1e25267
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1414 b1e25267
      have b1e26094 : y = (M.op y y) := by grind
      clear b1e26090
      have b1e26467 : x = (M.op y y) := by
        first
        | (have i₁ := b1e28 y
           have i₂ := b1e26094
           grind)
        | exact superpose b1e26094 b1e28
        | exact resolve b1e28 b1e26094
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e26623 : x = y := by
        first
        | (have i₁ := b1e26467
           have i₂ := b1e26094
           grind)
        | exact superpose b1e26094 b1e26467
        | exact resolve b1e26467 b1e26094
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26094 b1e26467
      have b1e27392 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e1110
           have i₂ := b1e26623
           grind)
        | exact superpose b1e26623 b1e1110
        | exact resolve b1e1110 b1e26623
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1110 b1e26623
      have b1e27440 : False := by grind
      exact b1e27440
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op y x) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e25 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ y) (σ x))) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
           have i₂ := b2e10 X0 (M.op (M.op X2 X0) X0) X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e28 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e25 X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e25
        | exact resolve b2e25 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25
      have b2e31 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b2e34 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b2e31
      have b2e35 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e34
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e34
        | exact resolve b2e34 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 X0
           have i₂ := b2e14 (σ X1) (σ X0)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X1) (σ X0)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e61 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b2e27 (M.op (M.op X2 X0) X0) X3 (M.op x x)
           have i₂ := b2e10 X0 x X2
           grind)
        | exact superpose b2e10 b2e27
        | exact resolve b2e27 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e62 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X1 X1) (σ y)) := by
        intro X1
        first
        | (have i₁ := b2e27 (σ y) X1 (M.op x x)
           have i₂ := b2e28 x
           grind)
        | exact superpose b2e28 b2e27
        | exact resolve b2e27 b2e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e89 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b2e62 x
           have i₂ := b2e28 x
           grind)
        | exact superpose b2e28 b2e62
        | exact resolve b2e62 b2e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e62
      have b2e90 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b2e61 X0 X2 x
           have i₂ := b2e10 X0 x X2
           grind)
        | exact superpose b2e10 b2e61
        | exact resolve b2e61 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e61
      have b2e94 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e35
           have i₂ := b2e89
           grind)
        | exact superpose b2e89 b2e35
        | exact resolve b2e35 b2e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35
      have b2e95 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e89
           grind)
        | exact superpose b2e89 b2e16
        | exact resolve b2e16 b2e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e97 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ y) (σ x)
           have i₂ := b2e89
           grind)
        | exact superpose b2e89 b2e13
        | (have j0 := b2e13 (σ y) (σ x)
           grind)
        | (have r₁ := b2e13 (σ y) (σ x)
           have r₂ := b2e89
           grind)
        | exact resolve b2e13 b2e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e89
      have b2e99 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
      clear b2e97
      have b2e100 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
        first
        | (have i₁ := b2e99
           have i₂ := b2e15 y x
           grind)
        | exact superpose b2e15 b2e99
        | exact resolve b2e99 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e99
      have b2e102 : (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b2e100
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e100
        | exact resolve b2e100 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e100
      have b2e151 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e94
           grind)
        | exact superpose b2e94 b2e11
        | exact resolve b2e11 b2e94
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e94
      have b2e152 : x = (k x y) := by
        first
        | (have i₁ := b2e151
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e151
        | exact resolve b2e151 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e151
      have b2e178 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e41 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e41
      have b2e188 : x = (M.op y x) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e152
           grind)
        | exact superpose b2e152 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e152
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e152
      have b2e189 : x = (M.op y x) := by
        first
        | (have r₁ := b2e188
           have r₂ := b2e17
           grind)
        | exact resolve b2e188 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e188
      have b2e197 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e10 x X0 y
           have i₂ := b2e189
           grind)
        | exact superpose b2e189 b2e10
        | exact resolve b2e10 b2e189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e189
      have b2e216 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e90 X1 x
           have i₂ := b2e27 X1 X0 x
           grind)
        | (have i₁ := b2e90 X0 X0
           have i₂ := b2e27 X0 X0 x
           grind)
        | exact superpose b2e27 b2e90
        | exact resolve b2e90 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e90
      have b2e263 : (k y x) = (τ (σ y)) := by
        first
        | (have i₁ := b2e11 (k y x)
           have i₂ := b2e102
           grind)
        | exact superpose b2e102 b2e11
        | exact resolve b2e11 b2e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e102
      have b2e274 : y = (k y x) := by
        first
        | (have i₁ := b2e263
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e263
        | exact resolve b2e263 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e263
      have b2e302 : x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e14 y x
           have i₂ := b2e274
           grind)
        | exact superpose b2e274 b2e14
        | (have j0 := b2e14 y x
           grind)
        | exact resolve b2e14 b2e274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e274
      have b2e836 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e27 X1 (M.op x x) X0
           have i₂ := b2e197 x
           grind)
        | exact superpose b2e197 b2e27
        | exact resolve b2e27 b2e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e846 : ∀ X0 : G, (M.op X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e216 (M.op x x) X0
           have i₂ := b2e197 x
           grind)
        | exact superpose b2e197 b2e216
        | exact resolve b2e216 b2e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197 b2e216
      have b2e970 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op x X0) X0) = (M.op (M.op x X0) X0) := by
        intro X0
        first
        | (have i₁ := b2e13 (M.op x X0) X0
           have i₂ := b2e846 X0
           grind)
        | exact superpose b2e846 b2e13
        | (have j0 := b2e13 (M.op x X0) X0
           grind)
        | (have r₁ := b2e13 (M.op x X0) X0
           have r₂ := b2e846 X0
           grind)
        | exact resolve b2e13 b2e846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e846
      have b2e980 : ∀ X0 : G, (k (M.op x X0) X0) = (M.op (M.op x X0) X0) := by
        intro X0
        first
        | (have j0 := b2e970 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e970
      have b2e986 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
        intro X0
        first
        | (have i₁ := b2e980 X0
           have i₂ := b2e836 x X0
           grind)
        | exact superpose b2e836 b2e980
        | exact resolve b2e980 b2e836
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e836 b2e980
      have b2e3094 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e95
           have i₂ := b2e302
           grind)
        | exact superpose b2e302 b2e95
        | exact resolve b2e95 b2e302
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e302
      have b2e3113 : y = (M.op x y) := by grind
      clear b2e3094
      have b2e3207 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e95
           have i₂ := b2e3113
           grind)
        | exact superpose b2e3113 b2e95
        | exact resolve b2e95 b2e3113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e95
      have b2e3209 : y = (k y y) := by
        first
        | (have i₁ := b2e986 y
           have i₂ := b2e3113
           grind)
        | exact superpose b2e3113 b2e986
        | exact resolve b2e986 b2e3113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e986 b2e3113
      have b2e3556 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e178 y y
           have i₂ := b2e3209
           grind)
        | exact superpose b2e3209 b2e178
        | (have j0 := b2e178 y y
           grind)
        | exact resolve b2e178 b2e3209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e178 b2e3209
      have b2e3559 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b2e3556
      have b2e4939 : (σ x) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e28 (σ y)
           have i₂ := b2e3559
           grind)
        | exact superpose b2e3559 b2e28
        | exact resolve b2e28 b2e3559
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28
      have b2e5006 : (σ x) = (σ y) := by
        first
        | (have i₁ := b2e4939
           have i₂ := b2e3559
           grind)
        | exact superpose b2e3559 b2e4939
        | exact resolve b2e4939 b2e3559
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3559 b2e4939
      have b2e5026 : False := by grind
      exact b2e5026
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op y x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k (τ X0) X1)
           have i₂ := b3e19 X0 X1
           grind)
        | exact superpose b3e19 b3e11
        | exact resolve b3e11 b3e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e25 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X0) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op (M.op X3 X0) X0))) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e10 (M.op (M.op X3 X0) X0) X1 (M.op x x)
           have i₂ := b3e10 X0 x X3
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e26 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
           have i₂ := b3e10 X0 (M.op (M.op X2 X0) X0) X2
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X0 (τ X1))
           have i₂ := b3e20 X1 X0
           grind)
        | exact superpose b3e20 b3e11
        | exact resolve b3e11 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e24 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e24
        | exact resolve b3e24 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24
      have b3e45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X1) (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e53 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e32 X1 X0
           have i₂ := b3e14 (σ X1) X0
           grind)
        | exact superpose b3e14 b3e32
        | (have j1 := b3e14 (σ X1) X0
           grind)
        | exact resolve b3e32 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e62 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b3e26 (M.op (M.op X2 X0) X0) X3 (M.op x x)
           have i₂ := b3e10 X0 x X2
           grind)
        | exact superpose b3e10 b3e26
        | exact resolve b3e26 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e73 : ∀ X0 X1 X2 : G, (M.op X2 X1) ≠ (M.op (M.op X0 X0) X1) ∨ (k X1 (M.op X2 X1)) = (M.op X1 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e13 X1 (M.op X2 X1)
           have i₂ := b3e26 X1 X0 X2
           grind)
        | (have i₁ := b3e13 X0 (M.op X1 X1)
           have i₂ := b3e26 X0 X1 X2
           grind)
        | exact superpose b3e26 b3e13
        | (have j0 := b3e13 X1 (M.op X2 X1)
           grind)
        | (have r₁ := b3e13 X0 (M.op (M.op X1 X1) X0)
           have r₂ := b3e26 X0 X1 (M.op X1 X1)
           grind)
        | exact resolve b3e13 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26
      have b3e79 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b3e62 X0 X2 x
           have i₂ := b3e10 X0 x X2
           grind)
        | exact superpose b3e10 b3e62
        | exact resolve b3e62 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e62
      have b3e153 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e45 x y
           grind)
        | exact superpose b3e45 b3e16
        | (have j1 := b3e45 x y
           grind)
        | exact resolve b3e16 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b3e45 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e45
      have b3e602 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e163 (τ X1) (τ X0)
           have i₂ := b3e36 X1 X0
           grind)
        | exact superpose b3e36 b3e163
        | (have j0 := b3e163 (τ X1) (τ X0)
           grind)
        | exact resolve b3e163 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36 b3e163
      have b3e609 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e602 X0 X1
           have i₂ := b3e12 (k X0 X1)
           grind)
        | exact superpose b3e12 b3e602
        | (have j0 := b3e602 X0 X1
           grind)
        | exact resolve b3e602 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e602
      have b3e611 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e609 X0 X1
           have i₂ := b3e12 X1
           grind)
        | exact superpose b3e12 b3e609
        | (have j0 := b3e609 X0 X1
           grind)
        | exact resolve b3e609 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e609
      have b3e612 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e611 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e611
        | (have j0 := b3e611 X0 X1
           grind)
        | exact resolve b3e611 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e611
      have b3e613 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e612 X0 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e612
        | (have j0 := b3e612 X0 X1
           grind)
        | exact resolve b3e612 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e612
      have b3e706 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e153
           have i₂ := b3e14 y x
           grind)
        | exact superpose b3e14 b3e153
        | (have j1 := b3e14 (σ y) (σ x)
           grind)
        | exact resolve b3e153 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e153
      have b3e707 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b3e706
      have b3e711 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e13 (σ y) (σ x)
           have i₂ := b3e707
           grind)
        | exact superpose b3e707 b3e13
        | (have j0 := b3e13 (σ y) (σ x)
           grind)
        | (have r₁ := b3e13 (σ y) (σ x)
           have r₂ := b3e707
           grind)
        | (have r₁ := b3e13 y x
           have r₂ := b3e707
           grind)
        | exact resolve b3e13 b3e707
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e718 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
      clear b3e711
      have b3e719 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e718
           have i₂ := b3e15 y x
           grind)
        | exact superpose b3e15 b3e718
        | exact resolve b3e718 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e718
      have b3e740 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X3 X3) (M.op X1 (M.op (M.op X0 X1) X1))) ∨ (M.op (M.op X1 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1)) = (k (M.op X1 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e73 X0 (M.op X0 (M.op (M.op X3 X0) X0)) (M.op X1 X1)
           have i₂ := b3e25 X0 X1 X3
           grind)
        | exact superpose b3e25 b3e73
        | exact resolve b3e73 b3e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e73
      have b3e773 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1)) = (k (M.op X1 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1)) := by
        intro X0 X1
        first
        | (have j0 := b3e740 X0 X1 x
           grind)
        | (have r₁ := b3e740 x X0 X1
           have r₂ := b3e25 X0 X1 x
           grind)
        | exact resolve b3e740 b3e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25 b3e740
      have b3e775 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (k X1 (M.op (M.op X0 X1) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e773 x X0
           have i₂ := b3e79 X0 x
           grind)
        | exact superpose b3e79 b3e773
        | exact resolve b3e773 b3e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e773
      have b3e776 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e775 X0 X1
           have i₂ := b3e79 X1 X0
           grind)
        | exact superpose b3e79 b3e775
        | exact resolve b3e775 b3e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e775
      have b3e883 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b3e32 X0 (M.op (M.op X1 (σ X0)) (σ X0))
           have i₂ := b3e776 X1 (σ X0)
           grind)
        | exact superpose b3e776 b3e32
        | exact resolve b3e32 b3e776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e32 b3e776
      have b3e886 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e883 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e883
        | exact resolve b3e883 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e883
      have b3e1528 : y = (k y (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e886 y (σ x)
           have i₂ := b3e707
           grind)
        | exact superpose b3e707 b3e886
        | exact resolve b3e886 b3e707
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e886
      have b3e4829 : (σ y) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e719
           grind)
        | exact superpose b3e719 b3e18
        | exact resolve b3e18 b3e719
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e4832 : (τ (σ (k y x))) = (k x (τ (σ y))) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e53 (σ y) x
           have i₂ := b3e719
           grind)
        | exact superpose b3e719 b3e53
        | exact resolve b3e53 b3e719
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e53 b3e719
      have b3e4852 : (k x y) = (τ (σ (k y x))) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e4832
           have i₂ := b3e11 y
           grind)
        | exact superpose b3e11 b3e4832
        | exact resolve b3e4832 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4832
      have b3e4855 : (k x y) = (τ (σ (k y x))) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b3e4852
           have r₂ := b3e4829
           grind)
        | exact resolve b3e4852 b3e4829
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4829 b3e4852
      have b3e4857 : (k x y) = (k y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e4855
           have i₂ := b3e11 (k y x)
           grind)
        | exact superpose b3e11 b3e4855
        | exact resolve b3e4855 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4855
      have b3e5276 : y ≠ (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e613 x y
           have i₂ := b3e4857
           grind)
        | exact superpose b3e4857 b3e613
        | (have j0 := b3e613 x y
           grind)
        | exact resolve b3e613 b3e4857
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e613 b3e4857
      have b3e5282 : y ≠ (k y x) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b3e5276
           have r₂ := b3e17
           grind)
        | exact resolve b3e5276 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e5276
      have b3e10673 : y = (k y (τ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e1528
           have i₂ := b3e707
           grind)
        | exact superpose b3e707 b3e1528
        | exact resolve b3e1528 b3e707
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e707 b3e1528
      have b3e10703 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by grind
      clear b3e10673
      have b3e10711 : y = (k y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b3e10703
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e10703
        | exact resolve b3e10703 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e10703
      have b3e10715 : x = (M.op x y) := by
        first
        | (have r₁ := b3e10711
           have r₂ := b3e5282
           grind)
        | exact resolve b3e10711 b3e5282
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e5282 b3e10711
      have b3e10893 : y = (M.op y (M.op x y)) := by
        first
        | (have i₁ := b3e79 y x
           have i₂ := b3e10715
           grind)
        | exact superpose b3e10715 b3e79
        | exact resolve b3e79 b3e10715
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e79
      have b3e10909 : y = (M.op y x) := by
        first
        | (have i₁ := b3e10893
           have i₂ := b3e10715
           grind)
        | exact superpose b3e10715 b3e10893
        | exact resolve b3e10893 b3e10715
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e10715 b3e10893
      have b3e10918 : False := by grind
      exact b3e10918

/-- `Equation311`: `x ◇ x = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
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
      have b0e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e47 (σ X0)
           grind)
        | exact superpose b0e47 b0e17
        | exact resolve b0e17 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e55 X0
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e55
        | exact resolve b0e55 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e55
      have b0e310 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e60 x
           grind)
        | exact superpose b0e60 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e60 x
           grind)
        | exact resolve b0e22 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e60
      have b0e323 : False := by grind
      exact b0e323
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
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
        have b1e53 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e56 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e56
        have b1e61 : (k x y) = (M.op y y) := by grind
        clear b1e53
        have b1e62 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e63 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e57 y
             grind)
          | exact superpose b1e57 b1e62
          | exact resolve b1e62 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e57 (σ X0)
             grind)
          | exact superpose b1e57 b1e18
          | exact resolve b1e18 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e65 X0
             have i₂ := b1e57 X0
             grind)
          | exact superpose b1e57 b1e65
          | exact resolve b1e65 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e65
        have b1e79 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 X0 (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e81 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e79 X0
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e79
          | (have j0 := b1e79 X0
             grind)
          | exact resolve b1e79 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79
        have b1e169 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e23
          | exact resolve b1e23 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e1770 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e81 (σ x)
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e81
          | (have j0 := b1e81 (σ x)
             grind)
          | (have r₁ := b1e81 (σ x)
             have r₂ := b1e63
             grind)
          | exact resolve b1e81 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63 b1e81
        have b1e1771 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e1770
        have b1e1772 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e1771
             have i₂ := b1e72 x
             grind)
          | exact superpose b1e72 b1e1771
          | exact resolve b1e1771 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1771
        have b1e1773 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e1772
             have r₂ := b1e169
             grind)
          | exact resolve b1e1772 b1e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1772
        have b1e1774 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e1773
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e1773
          | exact resolve b1e1773 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1773
        have b1e1775 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e1774
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e1774
          | exact resolve b1e1774 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e1774
        have b1e1776 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e1775
             have i₂ := b1e72 x
             grind)
          | exact superpose b1e72 b1e1775
          | exact resolve b1e1775 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72 b1e1775
        have b1e1777 : False := by grind
        exact b1e1777
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e51 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : (k x y) = (M.op y y) := by grind
        clear b2e51
        have b2e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e54 (σ X0)
             grind)
          | exact superpose b2e54 b2e18
          | exact resolve b2e18 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e59 X0
             have i₂ := b2e54 X0
             grind)
          | exact superpose b2e54 b2e59
          | exact resolve b2e59 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e59
        have b2e99 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ y) (σ y)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e285 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e66 y
             grind)
          | exact superpose b2e66 b2e22
          | exact resolve b2e22 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e1579 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e99 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99
        have b2e1580 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1579
             have r₂ := b2e21
             grind)
          | exact resolve b2e1579 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1579
        have b2e1582 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1580
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1580
          | exact resolve b2e1580 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1580
        have b2e1584 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1582
             have i₂ := b2e57
             grind)
          | exact superpose b2e57 b2e1582
          | exact resolve b2e1582 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e1582
        have b2e1585 : False := by grind
        exact b2e1585
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
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
        have b3e40 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e40
        have b3e46 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
        have b3e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e41 (σ X0)
             grind)
          | exact superpose b3e41 b3e18
          | exact resolve b3e18 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e49 X0
             have i₂ := b3e41 X0
             grind)
          | exact superpose b3e41 b3e49
          | exact resolve b3e49 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e55 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e148 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e46
             grind)
          | exact superpose b3e46 b3e15
          | exact resolve b3e15 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e150 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e148
        have b3e151 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e150
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e150
          | exact resolve b3e150 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e150
        have b3e152 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e151
             have i₂ := b3e41 y
             grind)
          | exact superpose b3e41 b3e151
          | exact resolve b3e151 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e151
        have b3e153 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e152
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e152
          | exact resolve b3e152 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152
        have b3e312 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e52 x
             grind)
          | exact superpose b3e52 b3e23
          | exact resolve b3e23 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e52
        have b3e385 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e55 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e386 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e385
             have r₂ := b3e20
             grind)
          | exact resolve b3e385 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e385
        have b3e390 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e153
             have i₂ := b3e386
             grind)
          | exact superpose b3e386 b3e153
          | exact resolve b3e153 b3e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153 b3e386
        have b3e394 : False := by grind
        exact b3e394
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e50 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e50
          have b4e56 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e52
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e52
            | exact resolve b4e52 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e58 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e56
               have i₂ := b4e51 y
               grind)
            | exact superpose b4e51 b4e56
            | exact resolve b4e56 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e56
          have b4e59 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e58
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e58
            | exact resolve b4e58 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58
          have b4e60 : False := by grind
          exact b4e60
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e48 (σ X0)
               grind)
            | exact superpose b5e48 b5e19
            | exact resolve b5e19 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e54 X0
               have i₂ := b5e48 X0
               grind)
            | exact superpose b5e48 b5e54
            | exact resolve b5e54 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e54
          have b5e63 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e119 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ y) (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e394 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e63 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e395 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e394
               have r₂ := b5e21
               grind)
            | exact resolve b5e394 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e394
          have b5e1836 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e119 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e119
          have b5e1837 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1836
               have r₂ := b5e23
               grind)
            | exact resolve b5e1836 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1836
          have b5e1839 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1837
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1837
            | exact resolve b5e1837 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1837
          have b5e1841 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1839
               have i₂ := b5e395
               grind)
            | exact superpose b5e395 b5e1839
            | exact resolve b5e1839 b5e395
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e395 b5e1839
          have b5e1844 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1841
               grind)
            | exact superpose b5e1841 b5e23
            | exact resolve b5e23 b5e1841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1841
          have b5e1860 : False := by grind
          exact b5e1860
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e37 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e37
        have b6e42 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
        have b6e141 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e15
          | exact resolve b6e15 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e143 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e141
        have b6e144 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e143
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e143
          | exact resolve b6e143 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e143
        have b6e145 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e144
             have i₂ := b6e38 y
             grind)
          | exact superpose b6e38 b6e144
          | exact resolve b6e144 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e144
        have b6e149 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e145
             grind)
          | exact superpose b6e145 b6e13
          | exact resolve b6e13 b6e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e145
        have b6e150 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e149
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e149
          | exact resolve b6e149 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e228 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e150
             grind)
          | exact superpose b6e150 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e150
        have b6e229 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e228
        have b6e231 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e229
             have r₂ := b6e21
             grind)
          | exact resolve b6e229 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e229
        have b6e233 : False := by grind
        exact b6e233
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e47 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e49 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e47
          have b7e52 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e49
            | exact resolve b7e49 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e48 y
               grind)
            | exact superpose b7e48 b7e52
            | exact resolve b7e52 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e48 (σ X0)
               grind)
            | exact superpose b7e48 b7e19
            | exact resolve b7e19 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e55 X0
               have i₂ := b7e48 X0
               grind)
            | exact superpose b7e48 b7e55
            | exact resolve b7e55 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e55
          have b7e65 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e17 X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 X0 (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e65 X0
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e65
            | (have j0 := b7e65 X0
               grind)
            | exact resolve b7e65 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e16 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X0 X0
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e131 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e108 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e145 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e23
            | exact resolve b7e23 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e151 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e145
               have i₂ := b7e60 x
               grind)
            | exact superpose b7e60 b7e145
            | exact resolve b7e145 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e145
          have b7e1497 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e67 (σ x)
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e67
            | (have j0 := b7e67 (σ x)
               grind)
            | (have r₁ := b7e67 (σ x)
               have r₂ := b7e53
               grind)
            | exact resolve b7e67 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53 b7e67
          have b7e1498 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e1497
          have b7e1499 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e1498
               have i₂ := b7e60 x
               grind)
            | exact superpose b7e60 b7e1498
            | exact resolve b7e1498 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1498
          have b7e1500 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e1499
               have r₂ := b7e151
               grind)
            | exact resolve b7e1499 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1499
          have b7e1501 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1500
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e1500
            | exact resolve b7e1500 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1500
          have b7e1502 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1501
               have i₂ := b7e60 x
               grind)
            | exact superpose b7e60 b7e1501
            | exact resolve b7e1501 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e1501
          have b7e1504 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e1502
               have i₂ := b7e131 x y
               grind)
            | exact superpose b7e131 b7e1502
            | (have j1 := b7e131 x y
               grind)
            | exact resolve b7e1502 b7e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e131
          have b7e1511 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1502
               grind)
            | exact superpose b7e1502 b7e14
            | exact resolve b7e14 b7e1502
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1502
          have b7e1512 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e1511
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e1511
            | exact resolve b7e1511 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1511
          have b7e1519 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e1504
               have r₂ := b7e151
               grind)
            | exact resolve b7e1504 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151 b7e1504
          have b7e1522 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e1519
               have r₂ := b7e22
               grind)
            | exact resolve b7e1519 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1519
          have b7e1525 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e1522
               have i₂ := b7e1512
               grind)
            | exact superpose b7e1512 b7e1522
            | exact resolve b7e1522 b7e1512
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1512 b7e1522
          have b7e1526 : False := by grind
          exact b7e1526
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e112 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1561 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e112 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112
          have b8e1562 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1561
               have r₂ := b8e23
               grind)
            | exact resolve b8e1561 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1561
          have b8e1564 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1562
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1562
            | exact resolve b8e1562 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1562
          have b8e1570 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1564
               grind)
            | exact superpose b8e1564 b8e20
            | exact resolve b8e20 b8e1564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1564
          have b8e1668 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1570
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1570
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1570 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1570
          have b8e1672 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1668
          have b8e1675 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1672
               have r₂ := b8e21
               grind)
            | exact resolve b8e1672 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1672
          have b8e1677 : False := by grind
          exact b8e1677
