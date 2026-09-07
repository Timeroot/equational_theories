import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation311`: `x ◇ x = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_y_pxy_Equation311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
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
        have b1e79 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
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
        have b1e81 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
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
        have b1e322 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (σ X0) (σ X0)
             have i₂ := b1e72 X0
             grind)
          | exact superpose b1e72 b1e12
          | exact resolve b1e12 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1751 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e1752 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e1751
        have b1e1753 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e1752
             have i₂ := b1e72 x
             grind)
          | exact superpose b1e72 b1e1752
          | exact resolve b1e1752 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72 b1e1752
        have b1e1754 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e1753
             have r₂ := b1e169
             grind)
          | exact resolve b1e1753 b1e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e169 b1e1753
        have b1e1755 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e1754
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e1754
          | exact resolve b1e1754 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1754
        have b1e1756 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e1755
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e1755
          | exact resolve b1e1755 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e1755
        have b1e1762 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e322 y X0
             have i₂ := b1e1756
             grind)
          | exact superpose b1e1756 b1e322
          | exact resolve b1e322 b1e1756
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e322 b1e1756
        have b1e6314 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1762 (σ x)
             grind)
          | exact superpose b1e1762 b1e21
          | (have r₁ := b1e21
             have r₂ := b1e1762 (σ x)
             grind)
          | exact resolve b1e21 b1e1762
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1762
        have b1e6319 : False := by grind
        exact b1e6319
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
        have b2e1561 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e99 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99
        have b2e1562 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1561
             have r₂ := b2e21
             grind)
          | exact resolve b2e1561 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1561
        have b2e1564 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1562
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1562
          | exact resolve b2e1562 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1562
        have b2e1566 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1564
             have i₂ := b2e57
             grind)
          | exact superpose b2e57 b2e1564
          | exact resolve b2e1564 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e1564
        have b2e1567 : False := by grind
        exact b2e1567
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e55 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ y = (k X0 y) := by
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
        have b3e156 : (k x y) = (τ (σ (M.op x y))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e153
             grind)
          | exact superpose b3e153 b3e13
          | exact resolve b3e13 b3e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153
        have b3e157 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b3e156
             have i₂ := b3e13 (M.op x y)
             grind)
          | exact superpose b3e13 b3e156
          | exact resolve b3e156 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156
        have b3e385 : (M.op x y) = (M.op x x) ∨ y = (k x y) := by
          first
          | (have j0 := b3e55 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e386 : y = (k x y) := by
          first
          | (have r₁ := b3e385
             have r₂ := b3e20
             grind)
          | exact resolve b3e385 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e385
        have b3e389 : y = (M.op x y) := by
          first
          | (have i₁ := b3e157
             have i₂ := b3e386
             grind)
          | exact superpose b3e386 b3e157
          | exact resolve b3e157 b3e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157 b3e386
        have b3e463 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e389
             grind)
          | exact superpose b3e389 b3e12
          | exact resolve b3e12 b3e389
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e389
        have b3e762 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e463 x
             grind)
          | exact superpose b3e463 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e463 x
             grind)
          | exact resolve b3e20 b3e463
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e463
        have b3e772 : False := by grind
        exact b3e772
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
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
          have b5e63 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ y = (k X0 y) := by
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
          have b5e394 : (M.op x y) = (M.op x x) ∨ y = (k x y) := by
            first
            | (have j0 := b5e63 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e395 : y = (k x y) := by
            first
            | (have r₁ := b5e394
               have r₂ := b5e21
               grind)
            | exact resolve b5e394 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e394
          have b5e1813 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e119 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e119
          have b5e1814 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1813
               have r₂ := b5e23
               grind)
            | exact resolve b5e1813 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1813
          have b5e1816 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1814
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1814
            | exact resolve b5e1814 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1814
          have b5e1818 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1816
               have i₂ := b5e395
               grind)
            | exact superpose b5e395 b5e1816
            | exact resolve b5e1816 b5e395
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e395 b5e1816
          have b5e1824 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ x) (σ y)
               have i₂ := b5e1818
               grind)
            | exact superpose b5e1818 b5e13
            | exact resolve b5e13 b5e1818
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1818
          have b5e2676 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1824 (σ x)
               grind)
            | exact superpose b5e1824 b5e23
            | (have r₁ := b5e23
               have r₂ := b5e1824 (σ x)
               grind)
            | exact resolve b5e23 b5e1824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1824
          have b5e2697 : False := by grind
          exact b5e2697
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
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
          have b7e65 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
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
          have b7e67 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
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
          have b7e1477 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e1478 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e1477
          have b7e1479 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e1478
               have i₂ := b7e60 x
               grind)
            | exact superpose b7e60 b7e1478
            | exact resolve b7e1478 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e1478
          have b7e1480 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e1479
               have r₂ := b7e151
               grind)
            | exact resolve b7e1479 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151 b7e1479
          have b7e1481 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1480
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e1480
            | exact resolve b7e1480 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1480
          have b7e1490 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1481
               grind)
            | exact superpose b7e1481 b7e14
            | exact resolve b7e14 b7e1481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1481
          have b7e1491 : y = (k x y) := by
            first
            | (have i₁ := b7e1490
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1490
            | exact resolve b7e1490 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1490
          have b7e1597 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e1491
               grind)
            | exact superpose b7e1491 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e1491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1491
          have b7e1598 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e1597
               have r₂ := b7e21
               grind)
            | exact resolve b7e1597 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1597
          have b7e1604 : y = (M.op x y) := by
            first
            | (have r₁ := b7e1598
               have r₂ := b7e22
               grind)
            | exact resolve b7e1598 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1598
          have b7e1705 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e1604
               grind)
            | exact superpose b7e1604 b7e13
            | exact resolve b7e13 b7e1604
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1604
          have b7e2627 : (M.op x x) ≠ (M.op x x) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e1705 x
               grind)
            | exact superpose b7e1705 b7e21
            | (have r₁ := b7e21
               have r₂ := b7e1705 x
               grind)
            | exact resolve b7e21 b7e1705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1705
          have b7e2642 : False := by grind
          exact b7e2642
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
          have b8e1544 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e112 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112
          have b8e1545 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1544
               have r₂ := b8e23
               grind)
            | exact resolve b8e1544 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1544
          have b8e1547 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1545
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1545
            | exact resolve b8e1545 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1545
          have b8e1553 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1547
               grind)
            | exact superpose b8e1547 b8e20
            | exact resolve b8e20 b8e1547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1547
          have b8e1655 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1553
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1553
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1553 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1553
          have b8e1656 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1655
          have b8e1658 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1656
               have r₂ := b8e21
               grind)
            | exact resolve b8e1656 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1656
          have b8e1661 : False := by grind
          exact b8e1661

/-- `Equation311`: `x ◇ x = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_pyy_pxy_Equation311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
      have b0e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e54 X0
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e54
        | exact resolve b0e54 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e54
      have b0e310 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e59 y
           grind)
        | exact superpose b0e59 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e59 y
           grind)
        | exact resolve b0e22 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e59
      have b0e324 : False := by grind
      exact b0e324
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op y y) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b1e54 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
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
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
        clear b1e54
        have b1e60 : (M.op x x) = (k x y) := by grind
        clear b1e51
        have b1e61 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e62 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e57 x
             grind)
          | exact superpose b1e57 b1e61
          | exact resolve b1e61 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b1e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e64 X0
             have i₂ := b1e57 X0
             grind)
          | exact superpose b1e57 b1e64
          | exact resolve b1e64 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e64
        have b1e78 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e82 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e78 X0
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e78
          | (have j0 := b1e78 X0
             grind)
          | exact resolve b1e78 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e173 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e23
          | exact resolve b1e23 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e2369 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e82 (σ y)
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e82
          | (have j0 := b1e82 (σ y)
             grind)
          | (have r₁ := b1e82 (σ y)
             have r₂ := b1e62
             grind)
          | exact resolve b1e82 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e82
        have b1e2387 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e2369
        have b1e2397 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e2387
             have i₂ := b1e71 y
             grind)
          | exact superpose b1e71 b1e2387
          | exact resolve b1e2387 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2387
        have b1e2409 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e2397
             have r₂ := b1e173
             grind)
          | exact resolve b1e2397 b1e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2397
        have b1e2417 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e2409
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e2409
          | exact resolve b1e2409 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2409
        have b1e2425 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e2417
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e2417
          | exact resolve b1e2417 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e2417
        have b1e2432 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e2425
             have i₂ := b1e71 y
             grind)
          | exact superpose b1e71 b1e2425
          | exact resolve b1e2425 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71 b1e2425
        have b1e2438 : False := by grind
        exact b1e2438
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e50 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b2e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : (M.op x x) = (k x y) := by grind
        clear b2e50
        have b2e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b2e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e58 X0
             have i₂ := b2e54 X0
             grind)
          | exact superpose b2e54 b2e58
          | exact resolve b2e58 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e58
        have b2e97 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) (σ x)
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
        have b2e288 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e65 x
             grind)
          | exact superpose b2e65 b2e22
          | exact resolve b2e22 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e2153 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e97 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e97
        have b2e2154 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2153
             have r₂ := b2e21
             grind)
          | exact resolve b2e2153 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2153
        have b2e2161 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2154
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2154
          | exact resolve b2e2154 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2154
        have b2e2168 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e2161
             have i₂ := b2e56
             grind)
          | exact superpose b2e56 b2e2161
          | exact resolve b2e2161 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e2161
        have b2e2169 : False := by grind
        exact b2e2169
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e38
        have b3e45 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
        have b3e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b3e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e48 X0
             have i₂ := b3e41 X0
             grind)
          | exact superpose b3e41 b3e48
          | exact resolve b3e48 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e54 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e152 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e15
          | exact resolve b3e15 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e154 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e152
        have b3e155 : (σ (k x y)) = (σ (k x x)) := by
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
        have b3e156 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e155
             have i₂ := b3e41 x
             grind)
          | exact superpose b3e41 b3e155
          | exact resolve b3e155 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e155
        have b3e157 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e156
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e156
          | exact resolve b3e156 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156
        have b3e309 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e51 y
             grind)
          | exact superpose b3e51 b3e23
          | exact resolve b3e23 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e51
        have b3e373 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e54 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e374 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e373
             have r₂ := b3e20
             grind)
          | exact resolve b3e373 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e373
        have b3e381 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e157
             have i₂ := b3e374
             grind)
          | exact superpose b3e374 b3e157
          | exact resolve b3e157 b3e374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157 b3e374
        have b3e385 : False := by grind
        exact b3e385
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b4e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e54 X0
               have i₂ := b4e51 X0
               grind)
            | exact superpose b4e51 b4e54
            | exact resolve b4e54 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e54
          have b4e332 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e59 x
               grind)
            | exact superpose b4e59 b4e28
            | (have r₁ := b4e28
               have r₂ := b4e59 x
               grind)
            | exact resolve b4e28 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e59
          have b4e349 : False := by grind
          exact b4e349
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b5e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e51 X0
               have i₂ := b5e48 X0
               grind)
            | exact superpose b5e48 b5e51
            | exact resolve b5e51 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e51
          have b5e61 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e61
          have b5e66 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e65
               have r₂ := b5e25
               grind)
            | exact resolve b5e65 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e65
          have b5e83 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ y) (σ y)
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
          have b5e315 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e56 y
               grind)
            | exact superpose b5e56 b5e23
            | exact resolve b5e23 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e1886 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e83 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e1887 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1886
               have r₂ := b5e24
               grind)
            | exact resolve b5e1886 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1886
          have b5e1889 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1887
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1887
            | exact resolve b5e1887 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1887
          have b5e1891 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1889
               have i₂ := b5e66
               grind)
            | exact superpose b5e66 b5e1889
            | exact resolve b5e1889 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e1889
          have b5e1892 : False := by grind
          exact b5e1892
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e21 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e36 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e36
        have b6e41 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
        have b6e145 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e15
          | exact resolve b6e15 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e147 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e145
        have b6e148 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e147
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e147
          | exact resolve b6e147 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e147
        have b6e149 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e148
             have i₂ := b6e38 x
             grind)
          | exact superpose b6e38 b6e148
          | exact resolve b6e148 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e148
        have b6e153 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e149
             grind)
          | exact superpose b6e149 b6e13
          | exact resolve b6e13 b6e149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e154 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e153
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e153
          | exact resolve b6e153 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e234 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e154
             grind)
          | exact superpose b6e154 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e154
        have b6e235 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e234
        have b6e237 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e235
             have r₂ := b6e21
             grind)
          | exact resolve b6e235 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e235
        have b6e239 : False := by grind
        exact b6e239
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
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
          have b7e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b7e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e51 X0
               have i₂ := b7e48 X0
               grind)
            | exact superpose b7e48 b7e51
            | exact resolve b7e51 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e51
          have b7e62 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e62
          have b7e66 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e25
               grind)
            | exact resolve b7e64 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e64
          have b7e67 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
          have b7e68 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e56 y
               grind)
            | exact superpose b7e56 b7e67
            | exact resolve b7e67 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56 b7e67
          have b7e150 : (k x y) = (τ (σ (M.op y y))) := by
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
          have b7e151 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e150
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e150
            | exact resolve b7e150 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e225 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e151
               grind)
            | exact superpose b7e151 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e226 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e225
          have b7e228 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e226
               have r₂ := b7e21
               grind)
            | exact resolve b7e226 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e226
          have b7e230 : False := by grind
          exact b7e230
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e104 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) (σ y)
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
          have b8e1990 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e104 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e1991 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1990
               have r₂ := b8e24
               grind)
            | exact resolve b8e1990 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1990
          have b8e1993 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1991
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1991
            | exact resolve b8e1991 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1991
          have b8e1998 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1993
               grind)
            | exact superpose b8e1993 b8e20
            | exact resolve b8e20 b8e1993
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1993
          have b8e2050 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e1998
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1998
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1998 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1998
          have b8e2054 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e2050
          have b8e2057 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e2054
               have r₂ := b8e21
               grind)
            | exact resolve b8e2054 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2054
          have b8e2058 : False := by grind
          exact b8e2058

/-- `Equation313`: `x ◇ x = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_pyx_x_pxy_Equation313 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law313 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law313.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : y = (M.op x y) := by
        first
        | (have i₁ := b0e11 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e11 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e24
           grind)
        | exact superpose b0e24 b0e18
        | exact resolve b0e18 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e64 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e60
           have i₂ := b0e23
           grind)
        | exact superpose b0e23 b0e60
        | exact resolve b0e60 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e60
      have b0e65 : False := by grind
      exact b0e65
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : y = (M.op x y) := by
          first
          | (have i₁ := b1e12 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e12 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e12 x y
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e34 : y = (M.op y y) := by
          first
          | (have i₁ := b1e33
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e33
          | exact resolve b1e33 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e46 : (M.op y y) = (k y y) := by grind
        have b1e48 : y = (k y y) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e34
             grind)
          | exact superpose b1e34 b1e46
          | exact resolve b1e46 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e46
        have b1e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e165 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e12 (σ y) (σ x)
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e12
          | exact resolve b1e12 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e166 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e165
             have i₂ := b1e12 (σ x) (σ x)
             grind)
          | exact superpose b1e12 b1e165
          | exact resolve b1e165 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e165
        have b1e834 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e52 y y
             have i₂ := b1e166
             grind)
          | exact superpose b1e166 b1e52
          | (have j0 := b1e52 x (k y y)
             grind)
          | exact resolve b1e52 b1e166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e166
        have b1e937 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        clear b1e834
        have b1e963 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
          first
          | (have r₁ := b1e937
             have r₂ := b1e21
             grind)
          | exact resolve b1e937 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e937
        have b1e980 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e963
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e963
          | exact resolve b1e963 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48 b1e963
        have b1e986 : False := by grind
        exact b1e986
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : y = (M.op x y) := by
          first
          | (have i₁ := b2e12 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (M.op X0 X1)
             have i₂ := b2e12 X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b2e12 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e12
          | exact resolve b2e12 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e29 : y = (M.op y y) := by
          first
          | (have i₁ := b2e28
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e28
          | exact resolve b2e28 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e39 : (M.op y y) = (k y y) := by grind
        have b2e41 : y = (k y y) := by
          first
          | (have i₁ := b2e39
             have i₂ := b2e29
             grind)
          | exact superpose b2e29 b2e39
          | exact resolve b2e39 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e39
        have b2e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e12 X0 X1
             have i₂ := b2e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X1 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e121 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e27 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e27 X0 X1
             have i₂ := b2e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b2e17 b2e27
          | (have j1 := b2e17 X1 X0
             grind)
          | exact resolve b2e27 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e147 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
          intro X0
          grind
        have b2e153 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e147 X0
             have i₂ := b2e27 X0 X0
             grind)
          | exact superpose b2e27 b2e147
          | exact resolve b2e147 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e147
        have b2e628 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e51 x x
             grind)
          | exact superpose b2e51 b2e21
          | (have j1 := b2e51 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e51 x y
             grind)
          | exact resolve b2e21 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e679 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e51 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e681 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e679 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e679
        have b2e693 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e628
        have b2e16238 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e681 y
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e681
          | (have j0 := b2e681 y
             grind)
          | exact resolve b2e681 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e681
        have b2e16242 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e16238
        have b2e16360 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e693
             have i₂ := b2e58 x x
             grind)
          | exact superpose b2e58 b2e693
          | (have j1 := b2e58 (σ x) (σ x)
             grind)
          | exact resolve b2e693 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58 b2e693
        have b2e16361 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e16360
        have b2e16363 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e16361
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16361
          | exact resolve b2e16361 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16361
        have b2e16364 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e16363
        have b2e16373 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e16364
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16364
          | exact resolve b2e16364 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16364
        have b2e16613 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e16373
             grind)
          | exact superpose b2e16373 b2e21
          | exact resolve b2e21 b2e16373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e16632 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e153 (σ x)
             have i₂ := b2e16373
             grind)
          | exact superpose b2e16373 b2e153
          | exact resolve b2e153 b2e16373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e153 b2e16373
        have b2e16688 : (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e16632
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e16632
          | exact resolve b2e16632 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16632
        have b2e19135 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e16688
             have i₂ := b2e121 x x
             grind)
          | exact superpose b2e121 b2e16688
          | (have j1 := b2e121 x x
             grind)
          | exact resolve b2e16688 b2e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121 b2e16688
        have b2e19155 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
        clear b2e19135
        have b2e19172 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e19155
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19155
          | exact resolve b2e19155 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19155
        have b2e19178 : x = y ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e19172
             have r₂ := b2e16613
             grind)
          | exact resolve b2e19172 b2e16613
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16613 b2e19172
        have b2e19184 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e19178
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19178
          | exact resolve b2e19178 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19178
        have b2e19185 : x = y := by grind
        clear b2e19184
        have b2e19199 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e19185
             grind)
          | exact superpose b2e19185 b2e22
          | exact resolve b2e22 b2e19185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e19230 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e16242
             have i₂ := b2e19185
             grind)
          | exact superpose b2e19185 b2e16242
          | exact resolve b2e16242 b2e19185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16242 b2e19185
        have b2e19236 : False := by grind
        exact b2e19236
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e12 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e12 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : (M.op y y) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b3e12 y x
             have i₂ := b3e26
             grind)
          | exact superpose b3e26 b3e12
          | exact resolve b3e12 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e33 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e12 x x
             grind)
          | exact superpose b3e12 b3e32
          | exact resolve b3e32 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e63 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e12 (σ x) (σ y)
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e12
          | exact resolve b3e12 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e64 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e63
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e63
          | exact resolve b3e63 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e82 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e84 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e82
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e82
          | exact resolve b3e82 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e85 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e64
             grind)
          | exact superpose b3e64 b3e84
          | exact resolve b3e84 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64 b3e84
        have b3e94 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e85
             grind)
          | exact superpose b3e85 b3e13
          | exact resolve b3e13 b3e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e96 : y = (k y y) := by
          first
          | (have i₁ := b3e94
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e94
          | exact resolve b3e94 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e163 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e96
             grind)
          | exact superpose b3e96 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96
        have b3e164 : y = (M.op y y) := by grind
        clear b3e163
        have b3e218 : y = (M.op x x) := by
          first
          | (have i₁ := b3e33
             have i₂ := b3e164
             grind)
          | exact superpose b3e164 b3e33
          | exact resolve b3e33 b3e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e164
        have b3e226 : False := by grind
        exact b3e226
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (σ x) ≠ (σ x) := by
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e38 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e43 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e38
          have b5e44 : x = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e55 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b5e613 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e55 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e614 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e613
               have r₂ := b5e24
               grind)
            | exact resolve b5e613 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e613
          have b5e615 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e614
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e614
            | exact resolve b5e614 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e614
          have b5e616 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e615
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e615
            | exact resolve b5e615 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e615
          have b5e617 : False := by grind
          exact b5e617
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e12 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 (M.op X0 X1)
             have i₂ := b6e12 X0 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e12 (σ x) (σ y)
             have i₂ := b6e25
             grind)
          | exact superpose b6e25 b6e12
          | exact resolve b6e12 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e28
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e28
          | exact resolve b6e28 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e33 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e25
             grind)
          | exact superpose b6e25 b6e19
          | exact resolve b6e19 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e35 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b6e37 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e35
          | exact resolve b6e35 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e39 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e37
             have i₂ := b6e29
             grind)
          | exact superpose b6e29 b6e37
          | exact resolve b6e37 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29 b6e37
        have b6e42 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e39
             grind)
          | exact superpose b6e39 b6e13
          | exact resolve b6e13 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e43 : y = (k y y) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e42
          | exact resolve b6e42 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b6e57 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e17 y y
             grind)
          | exact superpose b6e17 b6e43
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e43 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e64 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e12 X0 X1
             have i₂ := b6e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b6e17 b6e12
          | (have j1 := b6e17 X1 X0
             grind)
          | exact resolve b6e12 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e66 : y = (M.op y y) := by grind
        clear b6e57
        have b6e196 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
          intro X0
          grind
        have b6e202 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e196 X0
             have i₂ := b6e27 X0 X0
             grind)
          | exact superpose b6e27 b6e196
          | exact resolve b6e196 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27 b6e196
        have b6e674 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e56 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e56
          | exact resolve b6e56 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e772 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e674
        have b6e982 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e772
             grind)
          | exact superpose b6e772 b6e13
          | exact resolve b6e13 b6e772
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e998 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e982
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e982
          | exact resolve b6e982 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e982
        have b6e1008 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e64 x x
             have i₂ := b6e998
             grind)
          | exact superpose b6e998 b6e64
          | (have j0 := b6e64 x x
             grind)
          | exact resolve b6e64 b6e998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e998
        have b6e1009 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e1008
        have b6e1015 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1009
             have r₂ := b6e20
             grind)
          | exact resolve b6e1009 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1009
        have b6e1192 : x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e202 x
             have i₂ := b6e1015
             grind)
          | exact superpose b6e1015 b6e202
          | exact resolve b6e202 b6e1015
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e202 b6e1015
        have b6e1732 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e772
             have i₂ := b6e1192
             grind)
          | exact superpose b6e1192 b6e772
          | exact resolve b6e772 b6e1192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e772 b6e1192
        have b6e1745 : (σ x) = (σ y) := by grind
        clear b6e1732
        have b6e1954 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1745
             grind)
          | exact superpose b6e1745 b6e13
          | exact resolve b6e13 b6e1745
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1745
        have b6e1968 : x = y := by
          first
          | (have i₁ := b6e1954
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1954
          | exact resolve b6e1954 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1954
        have b6e2200 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e1968
             grind)
          | exact superpose b6e1968 b6e33
          | exact resolve b6e33 b6e1968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e2204 : x = (M.op x x) := by
          first
          | (have i₁ := b6e66
             have i₂ := b6e1968
             grind)
          | exact superpose b6e1968 b6e66
          | exact resolve b6e66 b6e1968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66 b6e1968
        have b6e2215 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b6e2200
             have i₂ := b6e2204
             grind)
          | exact superpose b6e2204 b6e2200
          | exact resolve b6e2200 b6e2204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2200 b6e2204
        have b6e2216 : False := by grind
        exact b6e2216
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e39
          have b7e43 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e23
               grind)
            | exact resolve b7e42 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
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
          have b7e56 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e44
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e44 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e62 : y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e26
               grind)
            | exact resolve b7e56 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e56
          have b7e63 : x = (M.op x y) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e64 : False := by grind
          exact b7e64
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e53 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b8e751 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e53 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e752 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e751
               have r₂ := b8e24
               grind)
            | exact resolve b8e751 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e751
          have b8e753 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e752
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e752
            | exact resolve b8e752 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e752
          have b8e754 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e753
               grind)
            | exact superpose b8e753 b8e20
            | exact resolve b8e20 b8e753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e753
          have b8e1072 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e754
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e754
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e754 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e754
          have b8e1080 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e1072
          have b8e1085 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1080
               have r₂ := b8e21
               grind)
            | exact resolve b8e1080 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1080
          have b8e1087 : False := by grind
          exact b8e1087

/-- `Equation313`: `x ◇ x = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_x_pxy_pyx_Equation313 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law313 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law313.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
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
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : y = (M.op x y) := by
        first
        | (have i₁ := b0e11 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e11 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e80 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e28
           grind)
        | exact superpose b0e28 b0e18
        | exact resolve b0e18 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e83 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e80
           have i₂ := b0e27
           grind)
        | exact superpose b0e27 b0e80
        | exact resolve b0e80 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e80
      have b0e84 : False := by grind
      exact b0e84
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b1e25 : x = (k x y) := by grind
        have b1e29 : y = (M.op x y) := by
          first
          | (have i₁ := b1e12 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e12 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 X0))) = X1 := by
          intro X0 X1
          grind
        have b1e76 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e90 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e76
             have r₂ := b1e21
             grind)
          | exact resolve b1e76 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e92 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e90
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e90
          | exact resolve b1e90 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e93 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e92
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e92
          | exact resolve b1e92 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e92
        have b1e100 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e93
             grind)
          | exact superpose b1e93 b1e19
          | exact resolve b1e19 b1e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e103 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e100
             have i₂ := b1e29
             grind)
          | exact superpose b1e29 b1e100
          | exact resolve b1e100 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e100
        have b1e111 : (σ x) = (k (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b1e33 (σ y) (σ x)
             have i₂ := b1e93
             grind)
          | exact superpose b1e93 b1e33
          | exact resolve b1e33 b1e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e93
        have b1e120 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e111
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e111
          | exact resolve b1e111 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e111
        have b1e124 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e120
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e120
          | exact resolve b1e120 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120
        have b1e127 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e124
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e124
          | (have j1 := b1e17 x x
             grind)
          | exact resolve b1e124 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124
        have b1e131 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e127
        have b1e135 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e131
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e131
          | exact resolve b1e131 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131
        have b1e136 : x = (M.op x x) := by
          first
          | (have r₁ := b1e135
             have r₂ := b1e103
             grind)
          | exact resolve b1e135 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e135
        have b1e160 : x = y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e136
             grind)
          | exact superpose b1e136 b1e20
          | exact resolve b1e20 b1e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e136
        have b1e239 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e103
             have i₂ := b1e160
             grind)
          | exact superpose b1e160 b1e103
          | exact resolve b1e103 b1e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e103 b1e160
        have b1e240 : False := by grind
        exact b1e240
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : x = (k x y) := by grind
        have b2e27 : y = (M.op x y) := by
          first
          | (have i₁ := b2e12 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b2e12 x y
             have i₂ := b2e27
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e32 : y = (M.op y y) := by
          first
          | (have i₁ := b2e31
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e31
          | exact resolve b2e31 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e35 : y = (k y y) := by grind
        clear b2e32
        have b2e49 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e926 : (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e49 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e927 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e926
             have r₂ := b2e22
             grind)
          | exact resolve b2e926 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e926
        have b2e928 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e927
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e927
          | exact resolve b2e927 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e927
        have b2e929 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e928
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e928
          | exact resolve b2e928 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e928
        have b2e930 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e12 (σ y) (σ x)
             have i₂ := b2e929
             grind)
          | exact superpose b2e929 b2e12
          | exact resolve b2e12 b2e929
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e929
        have b2e3134 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e56 y y
             have i₂ := b2e930
             grind)
          | exact superpose b2e930 b2e56
          | (have j0 := b2e56 (k y y) x
             grind)
          | exact resolve b2e56 b2e930
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e930
        have b2e3172 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        clear b2e3134
        have b2e3185 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
          first
          | (have r₁ := b2e3172
             have r₂ := b2e21
             grind)
          | exact resolve b2e3172 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3172
        have b2e3193 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e3185
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e3185
          | exact resolve b2e3185 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e3185
        have b2e3196 : False := by grind
        exact b2e3196
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e27 : (σ x) = (σ (k x y)) := by
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
        have b3e29 : x = (M.op y x) := by
          first
          | (have i₁ := b3e12 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e12 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b3e12 y x
             have i₂ := b3e29
             grind)
          | exact superpose b3e29 b3e12
          | exact resolve b3e12 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e35 : x = (M.op x x) := by
          first
          | (have i₁ := b3e34
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e34
          | exact resolve b3e34 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e38 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e35
             grind)
          | exact superpose b3e35 b3e20
          | exact resolve b3e20 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e70 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        have b3e81 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e70
             have r₂ := b3e20
             grind)
          | exact resolve b3e70 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e94 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b3e27
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e27
          | exact resolve b3e27 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e81
        have b3e100 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e19
          | exact resolve b3e19 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e101 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e12 (σ x) (σ y)
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e12
          | exact resolve b3e12 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e102 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e101
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e101
          | exact resolve b3e101 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101
        have b3e103 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e100
             have i₂ := b3e94
             grind)
          | exact superpose b3e94 b3e100
          | exact resolve b3e100 b3e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94 b3e100
        have b3e155 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e102
        have b3e158 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e155
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e155
          | exact resolve b3e155 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e155
        have b3e221 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e158
             have i₂ := b3e17 y y
             grind)
          | exact superpose b3e17 b3e158
          | (have j1 := b3e17 y y
             grind)
          | exact resolve b3e158 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e158
        have b3e225 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b3e221
        have b3e229 : (σ x) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e225
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e225
          | exact resolve b3e225 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e225
        have b3e230 : y = (M.op y y) := by
          first
          | (have r₁ := b3e229
             have r₂ := b3e103
             grind)
          | exact resolve b3e229 b3e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103 b3e229
        have b3e231 : x = y := by
          first
          | (have i₁ := b3e230
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e230
          | exact resolve b3e230 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e230
        have b3e232 : False := by grind
        exact b3e232
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b4e68 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b4e70 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          have b4e81 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e70
               have r₂ := b4e21
               grind)
            | exact resolve b4e70 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e82 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e68
               have r₂ := b4e23
               grind)
            | exact resolve b4e68 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e83 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e82
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e82
            | exact resolve b4e82 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e84 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e83
               have i₂ := b4e81
               grind)
            | exact superpose b4e81 b4e83
            | exact resolve b4e83 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81 b4e83
          have b4e85 : False := by grind
          exact b4e85
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : y = (k y x) := by grind
          have b5e29 : x = (M.op y x) := by
            first
            | (have i₁ := b5e13 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b5e13 y x
               have i₂ := b5e29
               grind)
            | exact superpose b5e29 b5e13
            | exact resolve b5e13 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e36 : x = (M.op x x) := by
            first
            | (have i₁ := b5e35
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e37 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e21
            | exact resolve b5e21 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e52 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ y) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ y) X0
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
          have b5e55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1
               have i₂ := b5e18 (M.op X0 X1) X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X1
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b5e874 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e52 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e875 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e874
               have r₂ := b5e23
               grind)
            | exact resolve b5e874 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e874
          have b5e876 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e875
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e875
            | exact resolve b5e875 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e875
          have b5e877 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e876
               have i₂ := b5e27
               grind)
            | exact superpose b5e27 b5e876
            | exact resolve b5e876 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e876
          have b5e879 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e13 (σ x) (σ y)
               have i₂ := b5e877
               grind)
            | exact superpose b5e877 b5e13
            | exact resolve b5e13 b5e877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e877
          have b5e2023 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e59 y y
               grind)
            | exact superpose b5e59 b5e24
            | (have j1 := b5e59 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e59 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e59 y x
               grind)
            | exact resolve b5e24 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e2190 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e2023
          have b5e2258 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (k y y)) := by
            first
            | (have i₁ := b5e2190
               have i₂ := b5e879
               grind)
            | exact superpose b5e879 b5e2190
            | exact resolve b5e2190 b5e879
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e879 b5e2190
          have b5e2313 : (σ x) ≠ (σ (k y y)) := by
            first
            | (have r₁ := b5e2258
               have r₂ := b5e23
               grind)
            | exact resolve b5e2258 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2258
          have b5e2373 : (σ x) ≠ (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e2313
               have i₂ := b5e55 y y
               grind)
            | exact superpose b5e55 b5e2313
            | (have j1 := b5e55 y y
               grind)
            | exact resolve b5e2313 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e2313
          have b5e2374 : (σ x) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b5e2373
          have b5e2377 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e2374
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2374
            | exact resolve b5e2374 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2374
          have b5e2378 : y = (M.op y y) := by grind
          clear b5e2377
          have b5e2387 : x = y := by
            first
            | (have i₁ := b5e2378
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2378
            | exact resolve b5e2378 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2378
          have b5e2392 : False := by grind
          exact b5e2392
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
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
        have b6e27 : (k x y) = (τ (σ x)) := by
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
        have b6e28 : x = (k x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e27
          | exact resolve b6e27 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e30 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e12 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e12 (σ x) (σ y)
             have i₂ := b6e30
             grind)
          | exact superpose b6e30 b6e12
          | exact resolve b6e12 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e41 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e40
          | exact resolve b6e40 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e61 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
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
        have b6e65 : x = (M.op y x) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e61
             have r₂ := b6e20
             grind)
          | exact resolve b6e61 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e68 : x = (M.op y x) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e21
             grind)
          | exact resolve b6e65 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e70 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e12 y x
             have i₂ := b6e68
             grind)
          | exact superpose b6e68 b6e12
          | exact resolve b6e12 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e188 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b6e41
        have b6e193 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e188
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e188
          | exact resolve b6e188 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e188
        have b6e256 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e193
             grind)
          | exact superpose b6e193 b6e13
          | exact resolve b6e13 b6e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e193
        have b6e258 : y = (k y y) := by
          first
          | (have i₁ := b6e256
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e256
          | exact resolve b6e256 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e256
        have b6e302 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e258
             grind)
          | exact superpose b6e258 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e258
        have b6e303 : y = (M.op y y) := by grind
        clear b6e302
        have b6e319 : y = (M.op x x) := by
          first
          | (have i₁ := b6e70
             have i₂ := b6e303
             grind)
          | exact superpose b6e303 b6e70
          | exact resolve b6e70 b6e303
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70 b6e303
        have b6e330 : False := by grind
        exact b6e330
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : (σ y) = (k (σ y) (σ x)) := by grind
          have b7e28 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e27
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e27
            | exact resolve b7e27 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e30 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e13 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e28
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e35 : y = (k y x) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e34
            | exact resolve b7e34 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e42 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e13 (σ y) (σ x)
               have i₂ := b7e30
               grind)
            | exact superpose b7e30 b7e13
            | exact resolve b7e13 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e43 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e42
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e42
            | exact resolve b7e42 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e64 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e35
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e35
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e35 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e68 : y = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e71 : y = (M.op x y) := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e21
               grind)
            | exact resolve b7e68 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e73 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e13 x y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e13
            | exact resolve b7e13 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e111 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e22
            | exact resolve b7e22 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e266 : (σ x) = (k (σ x) (σ x)) := by grind
          clear b7e43
          have b7e274 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e266
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e266
            | exact resolve b7e266 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266
          have b7e355 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e274
               grind)
            | exact superpose b7e274 b7e14
            | exact resolve b7e14 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e274
          have b7e357 : x = (k x x) := by
            first
            | (have i₁ := b7e355
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e355
            | exact resolve b7e355 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e355
          have b7e405 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e357
               grind)
            | exact superpose b7e357 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e357
          have b7e406 : x = (M.op x x) := by grind
          clear b7e405
          have b7e411 : False := by grind
          exact b7e411
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e49 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
          have b8e760 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e49 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e761 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e760
               have r₂ := b8e23
               grind)
            | exact resolve b8e760 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e760
          have b8e762 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e761
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e761
            | exact resolve b8e761 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e761
          have b8e763 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e762
               grind)
            | exact superpose b8e762 b8e20
            | exact resolve b8e20 b8e762
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e762
          have b8e894 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e763
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e763
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e763 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e763
          have b8e904 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e894
          have b8e910 : y = (M.op x x) := by
            first
            | (have r₁ := b8e904
               have r₂ := b8e22
               grind)
            | exact resolve b8e904 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e904
          have b8e913 : False := by grind
          exact b8e913

/-- `Equation314`: `x ◇ x = y ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pxy_x_y_pxy_Equation314 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law314 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law314.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, y = (M.op X0 y) := by
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
      have b0e38 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e11
        | exact resolve b0e11 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e38 X0 x
           have i₂ := b0e27 x
           grind)
        | exact superpose b0e27 b0e38
        | exact resolve b0e38 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e69 : y = (σ y) := by
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
      have b0e127 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e69
           grind)
        | exact superpose b0e69 b0e18
        | exact resolve b0e18 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e132 : y ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e127
           have i₂ := b0e27 (σ x)
           grind)
        | exact superpose b0e27 b0e127
        | exact resolve b0e127 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127
      have b0e133 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e132
           have i₂ := b0e27 x
           grind)
        | exact superpose b0e27 b0e132
        | exact resolve b0e132 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e132
      have b0e134 : False := by grind
      exact b0e134
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : ∀ X0 : G, y = (M.op X0 y) := by
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
        have b1e32 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 (M.op X1 X2))) = X1 := by
          intro X0 X1 X2
          grind
        have b1e35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e38 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 y
             have i₂ := b1e28 X0
             grind)
          | exact superpose b1e28 b1e12
          | exact resolve b1e12 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b1e38 X0 x
             have i₂ := b1e28 x
             grind)
          | exact superpose b1e28 b1e38
          | exact resolve b1e38 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = y := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e12
          | exact resolve b1e12 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          grind
        have b1e48 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e39 (σ x)
             grind)
          | exact superpose b1e39 b1e21
          | exact resolve b1e21 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : ∀ X0 : G, y ≠ (M.op y X0) ∨ y = X0 ∨ (k y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e28 y
             grind)
          | exact superpose b1e28 b1e16
          | (have j0 := b1e16 y X0
             grind)
          | exact resolve b1e16 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e60 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e62 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e60
        have b1e67 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e62
             have r₂ := b1e21
             grind)
          | exact resolve b1e62 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e72 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e67
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e67
          | exact resolve b1e67 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e76 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e72
             have i₂ := b1e44 x
             grind)
          | exact superpose b1e44 b1e72
          | exact resolve b1e72 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e72
        have b1e96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
        have b1e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e96 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e96
        have b1e103 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e102 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102
        have b1e107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ y = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e103 X0 X1
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e103
          | (have j0 := b1e103 X0 X1
             grind)
          | exact resolve b1e103 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e103
        have b1e133 : y ≠ (σ x) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e48
          | exact resolve b1e48 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e267 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op (τ X0) X2)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e35 X0 (M.op X1 (M.op (τ X0) X2))
             have i₂ := b1e32 X1 (τ X0) X2
             grind)
          | exact superpose b1e32 b1e35
          | exact resolve b1e35 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e35
        have b1e273 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e267 X0 x x
             have i₂ := b1e43 (τ X0) x x
             grind)
          | exact superpose b1e43 b1e267
          | exact resolve b1e267 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e267
        have b1e276 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e273 X0
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e273
          | exact resolve b1e273 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76 b1e273
        have b1e279 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e276 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e276
          | exact resolve b1e276 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e276
        have b1e950 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = X0 ∨ y = (σ x) := by
          intro X0
          first
          | (have i₁ := b1e107 X0 (σ x)
             have i₂ := b1e279 X0
             grind)
          | exact superpose b1e279 b1e107
          | (have j0 := b1e107 X0 (σ x)
             grind)
          | exact resolve b1e107 b1e279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107
        have b1e973 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = X0 := by
          intro X0
          first
          | (have j0 := b1e950 X0
             grind)
          | (have r₁ := b1e950 y
             have r₂ := b1e133
             grind)
          | (have r₁ := b1e950 X0
             have r₂ := b1e133
             grind)
          | exact resolve b1e950 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e950
        have b1e2694 : y ≠ y ∨ y = (σ x) ∨ (σ x) = (k y (σ x)) ∨ y = (σ x) := by
          first
          | (have i₁ := b1e54 (σ x)
             have i₂ := b1e973 y
             grind)
          | exact superpose b1e973 b1e54
          | (have j0 := b1e54 (σ x)
             have j1 := b1e973 y
             grind)
          | (have r₁ := b1e54 (σ x)
             have r₂ := b1e973 y
             grind)
          | exact resolve b1e54 b1e973
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e973
        have b1e2695 : y ≠ y ∨ y = (σ x) ∨ (σ x) = (k y (σ x)) := by grind
        clear b1e2694
        have b1e2696 : y = (σ x) ∨ (σ x) = (k y (σ x)) := by grind
        clear b1e2695
        have b1e2697 : (σ x) = (k y (σ x)) := by
          first
          | (have r₁ := b1e2696
             have r₂ := b1e133
             grind)
          | exact resolve b1e2696 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2696
        have b1e2710 : y = (σ x) := by
          first
          | (have i₁ := b1e2697
             have i₂ := b1e279 y
             grind)
          | exact superpose b1e279 b1e2697
          | exact resolve b1e2697 b1e279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e279 b1e2697
        have b1e2722 : False := by grind
        exact b1e2722
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 : G, y = (M.op X0 y) := by
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
        have b2e34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e37 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 y
             have i₂ := b2e27 X0
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b2e37 X0 x
             have i₂ := b2e27 x
             grind)
          | exact superpose b2e27 b2e37
          | exact resolve b2e37 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e42 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          grind
        have b2e45 : y ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e38 (σ x)
             grind)
          | exact superpose b2e38 b2e21
          | exact resolve b2e21 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : ∀ X0 : G, y ≠ (M.op y X0) ∨ y = X0 ∨ (k y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e27 y
             grind)
          | exact superpose b2e27 b2e16
          | (have j0 := b2e16 y X0
             grind)
          | exact resolve b2e16 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e16 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 (M.op X0 X1)
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e86 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e93 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e92 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92
        have b2e97 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ y = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e93 X0 X1
             have i₂ := b2e38 X0
             grind)
          | exact superpose b2e38 b2e93
          | (have j0 := b2e93 X0 X1
             grind)
          | exact resolve b2e93 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e93
        have b2e258 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e34 X0 y
             have i₂ := b2e42 (τ X0)
             grind)
          | exact superpose b2e42 b2e34
          | exact resolve b2e34 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e42
        have b2e262 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e258 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e258
          | exact resolve b2e258 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e258
        have b2e911 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e97 X0 (σ y)
             have i₂ := b2e262 X0
             grind)
          | exact superpose b2e262 b2e97
          | (have j0 := b2e97 X0 (σ y)
             grind)
          | exact resolve b2e97 b2e262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e97
        have b2e941 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b2e911 X0
             grind)
          | (have r₁ := b2e911 y
             have r₂ := b2e45
             grind)
          | (have r₁ := b2e911 X0
             have r₂ := b2e45
             grind)
          | exact resolve b2e911 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e911
        have b2e1856 : y ≠ y ∨ y = (σ y) ∨ (σ y) = (k y (σ y)) ∨ y = (σ y) := by
          first
          | (have i₁ := b2e50 (σ y)
             have i₂ := b2e941 y
             grind)
          | exact superpose b2e941 b2e50
          | (have j0 := b2e50 (σ y)
             have j1 := b2e941 y
             grind)
          | (have r₁ := b2e50 (σ y)
             have r₂ := b2e941 y
             grind)
          | exact resolve b2e50 b2e941
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e941
        have b2e1857 : y ≠ y ∨ y = (σ y) ∨ (σ y) = (k y (σ y)) := by grind
        clear b2e1856
        have b2e1858 : y = (σ y) ∨ (σ y) = (k y (σ y)) := by grind
        clear b2e1857
        have b2e1861 : (σ y) = (k y (σ y)) := by
          first
          | (have r₁ := b2e1858
             have r₂ := b2e45
             grind)
          | exact resolve b2e1858 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1858
        have b2e1862 : y = (σ y) := by
          first
          | (have i₁ := b2e1861
             have i₂ := b2e262 y
             grind)
          | exact superpose b2e262 b2e1861
          | exact resolve b2e1861 b2e262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e262 b2e1861
        have b2e1863 : False := by grind
        exact b2e1863
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ x) = (σ (k x y)) := by
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
        have b3e27 : (k x y) = (τ (σ x)) := by
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
        have b3e28 : x = (k x y) := by
          first
          | (have i₁ := b3e27
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e27
          | exact resolve b3e27 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e32 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) x (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (σ y)
             have i₂ := b3e32 X0
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e46 X0 x
             have i₂ := b3e32 x
             grind)
          | exact superpose b3e32 b3e46
          | exact resolve b3e46 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e46
        have b3e53 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e20
          | exact resolve b3e20 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          grind
        have b3e63 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e73 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e63
        have b3e77 : y = (k x y) := by
          first
          | (have r₁ := b3e73
             have r₂ := b3e20
             grind)
          | exact resolve b3e73 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e81 : x = y := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e77
          | exact resolve b3e77 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e77
        have b3e114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
        have b3e120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e114 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114
        have b3e121 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e120 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120
        have b3e125 : ∀ X0 X1 : G, (σ y) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e121 X0 X1
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e121
          | (have j0 := b3e121 X0 X1
             grind)
          | exact resolve b3e121 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e121
        have b3e144 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (σ x) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e125 X0 X1
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e125
          | (have j0 := b3e125 X0 X1
             grind)
          | exact resolve b3e125 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e125
        have b3e182 : x ≠ (σ x) := by
          first
          | (have i₁ := b3e53
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e53
          | exact resolve b3e53 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e476 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e55 (σ X0)
             grind)
          | exact superpose b3e55 b3e18
          | exact resolve b3e18 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e479 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e476 X0
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e476
          | exact resolve b3e476 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e476
        have b3e1097 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 x)
             have i₂ := b3e479 X0
             grind)
          | exact superpose b3e479 b3e13
          | exact resolve b3e13 b3e479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e479
        have b3e1098 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e1097 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e1097
          | exact resolve b3e1097 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1097
        have b3e1181 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = X0 ∨ x = (σ x) := by
          intro X0
          first
          | (have i₁ := b3e144 X0 x
             have i₂ := b3e1098 X0
             grind)
          | exact superpose b3e1098 b3e144
          | (have j0 := b3e144 X0 x
             grind)
          | exact resolve b3e144 b3e1098
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144
        have b3e1188 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b3e1181 X0
             grind)
          | (have r₁ := b3e1181 (σ x)
             have r₂ := b3e182
             grind)
          | (have r₁ := b3e1181 X0
             have r₂ := b3e182
             grind)
          | exact resolve b3e1181 b3e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1181
        have b3e2225 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = x ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 x
             have i₂ := b3e1188 X0
             grind)
          | exact superpose b3e1188 b3e16
          | (have j0 := b3e16 X0 x
             have j1 := b3e1188 (M.op X0 X0)
             grind)
          | exact resolve b3e16 b3e1188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1188
        have b3e2248 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = x ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2225 X0
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e2225
          | (have j0 := b3e2225 X0
             grind)
          | (have r₁ := b3e2225 (σ y)
             have r₂ := b3e47 (σ y)
             grind)
          | exact resolve b3e2225 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2225
        have b3e2254 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = x ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2248 X0
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e2248
          | (have j0 := b3e2248 X0
             grind)
          | exact resolve b3e2248 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2248
        have b3e2257 : ∀ X0 : G, x = (σ y) ∨ (σ x) ≠ X0 ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2254 X0
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e2254
          | (have j0 := b3e2254 X0
             grind)
          | exact resolve b3e2254 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e2254
        have b3e2259 : ∀ X0 : G, x = (σ x) ∨ (σ x) ≠ X0 ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2257 X0
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e2257
          | (have j0 := b3e2257 X0
             grind)
          | exact resolve b3e2257 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e2257
        have b3e2260 : ∀ X0 : G, (σ x) ≠ X0 ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b3e2259 X0
             grind)
          | (have r₁ := b3e2259 X0
             have r₂ := b3e182
             grind)
          | (have r₁ := b3e2259 (σ x)
             have r₂ := b3e182
             grind)
          | exact resolve b3e2259 b3e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2259
        have b3e2261 : ∀ X0 : G, x = X0 ∨ (σ x) ≠ X0 ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2260 X0
             have i₂ := b3e1098 X0
             grind)
          | exact superpose b3e1098 b3e2260
          | (have j0 := b3e2260 X0
             grind)
          | (have r₁ := b3e2260 (k (σ x) x)
             have r₂ := b3e1098 (σ x)
             grind)
          | exact resolve b3e2260 b3e1098
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1098 b3e2260
        have b3e2262 : ∀ X0 : G, (σ x) ≠ X0 ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b3e2261 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2261
        have b3e2390 : x = (σ x) := by
          first
          | (have j0 := b3e2262 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2262
        have b3e2391 : False := by grind
        exact b3e2391
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
          have b4e28 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 X1 X3 X4
               have i₂ := b4e13 X1 X0 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op X0 x)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0 x
               have i₂ := b4e13 X1 x X1
               grind)
            | (have i₁ := b4e32 X0 X1 (M.op X0 X0)
               have i₂ := b4e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e55 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            grind
          have b4e60 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b4e27
               have i₂ := b4e36 (σ x) X0
               grind)
            | (have i₁ := b4e27
               have i₂ := b4e36 X0 (σ x)
               grind)
            | exact superpose b4e36 b4e27
            | exact resolve b4e27 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e78 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (M.op X1 X1) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X1 (M.op X0 X2)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e17
            | (have j0 := b4e17 X1 (M.op X0 X2)
               grind)
            | (have r₁ := b4e17 X1 (M.op X1 X2)
               have r₂ := b4e13 X1 X1 X2
               grind)
            | exact resolve b4e17 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e87 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X1) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e78 X0 X1 X2
               grind)
            | (have r₁ := b4e78 X0 X1 X2
               have r₂ := b4e36 X0 X1
               grind)
            | (have r₁ := b4e78 X1 X0 X2
               have r₂ := b4e36 X0 X1
               grind)
            | exact resolve b4e78 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
          have b4e116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e112 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e117 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e116 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116
          have b4e159 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 X0 (M.op X1 X1)
               have i₂ := b4e55 X1 (τ X0)
               grind)
            | exact superpose b4e55 b4e37
            | exact resolve b4e37 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e166 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e159 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e159
            | exact resolve b4e159 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e159
          have b4e174 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e60 X1
               have i₂ := b4e36 x X0
               grind)
            | (have i₁ := b4e60 X1
               have i₂ := b4e36 X0 x
               grind)
            | exact superpose b4e36 b4e60
            | exact resolve b4e60 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e315 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) ≠ (σ (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e174 (M.op X1 x) X3
               have i₂ := b4e28 (M.op X1 x) X1 x X0 X2
               grind)
            | (have i₁ := b4e174 (M.op X1 x) X3
               have i₂ := b4e28 X0 X1 X2 (M.op X1 x) x
               grind)
            | exact superpose b4e28 b4e174
            | exact resolve b4e174 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e811 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X2 ∨ (k X1 X2) = X2 ∨ (M.op X1 X2) = (k X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X1 X2
               have i₂ := b4e87 X1 X0 X2
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e87 X0 X1 X2
               grind)
            | exact superpose b4e87 b4e17
            | (have j0 := b4e17 X1 X2
               have j1 := b4e87 X1 X0 X2
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e87 X1 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X2
               have r₂ := b4e87 X0 X0 X2
               grind)
            | exact resolve b4e17 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87
          have b4e894 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X1) = X2 ∨ (k X1 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e811 X0 X1 X2
               grind)
            | (have r₁ := b4e811 X0 X1 X2
               have r₂ := b4e36 X0 X1
               grind)
            | (have r₁ := b4e811 X1 X0 X2
               have r₂ := b4e36 X0 X1
               grind)
            | exact resolve b4e811 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e811
          have b4e940 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e117 X0 (σ (M.op X1 X1))
               have i₂ := b4e166 X0 X1
               grind)
            | exact superpose b4e166 b4e117
            | (have j0 := b4e117 X0 (σ (M.op X1 X1))
               grind)
            | exact resolve b4e117 b4e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117
          have b4e1034 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e940 X0 X1
               grind)
            | (have r₁ := b4e940 (σ (M.op X0 X0)) X0
               have r₂ := b4e174 X0 (σ (M.op X0 X0))
               grind)
            | (have r₁ := b4e940 X1 X0
               have r₂ := b4e174 X0 X1
               grind)
            | (have r₁ := b4e940 (M.op X1 X1) X0
               have r₂ := b4e174 X0 X1
               grind)
            | exact resolve b4e940 b4e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e940
          have b4e16134 : ∀ X0 X1 X2 : G, (k X2 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (k X0 (σ (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e894 X0 X0 (σ (M.op X1 X1))
               have i₂ := b4e1034 X0 X1
               grind)
            | exact superpose b4e1034 b4e894
            | (have j0 := b4e894 X0 X0 (σ (M.op X1 X1))
               have j1 := b4e1034 (M.op X0 X0) X1
               grind)
            | exact resolve b4e894 b4e1034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e894 b4e1034
          have b4e16170 : ∀ X0 X1 X2 : G, (k X2 X0) = X0 ∨ (σ (M.op X1 X1)) = (k X0 (σ (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e16134 X0 X1 X2
               grind)
            | (have r₁ := b4e16134 X1 X0 X2
               have r₂ := b4e174 X0 X1
               grind)
            | (have r₁ := b4e16134 (M.op X1 X1) X0 X2
               have r₂ := b4e174 X0 X1
               grind)
            | exact resolve b4e16134 b4e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16134
          have b4e16194 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = X0 ∨ (k X2 X0) = X0 ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16170 X0 X1 X2
               have i₂ := b4e166 X0 X1
               grind)
            | exact superpose b4e166 b4e16170
            | (have j0 := b4e16170 X0 X1 X2
               grind)
            | exact resolve b4e16170 b4e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e166 b4e16170
          have b4e16195 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = X0 ∨ (k X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e16194 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16194
          have b4e16923 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e55 X0 X1
               have i₂ := b4e16195 (M.op X0 X0) X2 X1
               grind)
            | exact superpose b4e16195 b4e55
            | (have j1 := b4e16195 (M.op X0 X0) X2 X2
               grind)
            | exact resolve b4e55 b4e16195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55 b4e16195
          have b4e16972 : ∀ X0 X1 : G, (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e16923 X0 X1 x
               grind)
            | (have r₁ := b4e16923 X1 (σ (M.op X0 X0)) x
               have r₂ := b4e174 X0 X1
               grind)
            | (have r₁ := b4e16923 X1 X1 X0
               have r₂ := b4e174 X0 X1
               grind)
            | exact resolve b4e16923 b4e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e174 b4e16923
          have b4e17600 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e315 x x x X0
               have i₂ := b4e16972 X1 (σ (M.op x (M.op x x)))
               grind)
            | exact superpose b4e16972 b4e315
            | (have r₁ := b4e315 X0 X1 x X0
               have r₂ := b4e16972 X0 (σ (M.op X0 (M.op X1 x)))
               grind)
            | exact resolve b4e315 b4e16972
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e315 b4e16972
          have b4e17750 : False := by grind
          exact b4e17750
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
          have b5e31 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e31 X1 X0 x
               have i₂ := b5e13 X1 x X1
               grind)
            | (have i₁ := b5e31 X0 X1 (M.op X0 X0)
               have i₂ := b5e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e37 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e52 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
            intro X0
            first
            | (have i₁ := b5e21
               have i₂ := b5e35 x X0
               grind)
            | (have i₁ := b5e21
               have i₂ := b5e35 X0 x
               grind)
            | exact superpose b5e35 b5e21
            | exact resolve b5e21 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e54 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            grind
          have b5e60 : ∀ X0 X1 X2 : G, y ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e52 X1
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e52
            | exact resolve b5e52 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e70 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e74 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X2) = (M.op X1 X1) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X1 (M.op X0 X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 X1 (M.op X0 X2)
               grind)
            | (have r₁ := b5e17 X1 (M.op X1 X2)
               have r₂ := b5e13 X1 X1 X2
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e70
          have b5e80 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X1) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e74 X0 X1 X2
               grind)
            | (have r₁ := b5e74 X0 X1 X2
               have r₂ := b5e35 X0 X1
               grind)
            | (have r₁ := b5e74 X1 X0 X2
               have r₂ := b5e35 X0 X1
               grind)
            | exact resolve b5e74 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74
          have b5e81 : y = (k x y) := by
            first
            | (have r₁ := b5e79
               have r₂ := b5e21
               grind)
            | exact resolve b5e79 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b5e114 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X0 (M.op X1 X2))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e54 X1 X3
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e54
            | exact resolve b5e54 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e176 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e37 X1 X0
               grind)
            | exact superpose b5e37 b5e14
            | exact resolve b5e14 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e844 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e80 (σ x) X0 (σ y)
               grind)
            | exact superpose b5e80 b5e24
            | (have j1 := b5e80 (σ x) X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e80 (σ x) (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e898 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have j0 := b5e844 X0
               grind)
            | (have r₁ := b5e844 X0
               have r₂ := b5e35 X0 (σ x)
               grind)
            | (have r₁ := b5e844 x
               have r₂ := b5e35 (σ x) x
               grind)
            | exact resolve b5e844 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e844
          have b5e1051 : ∀ X0 X1 X2 X3 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e176 X0 (M.op X1 (M.op X2 X3))
               have i₂ := b5e114 X1 X2 X3 (σ X0)
               grind)
            | exact superpose b5e114 b5e176
            | exact resolve b5e176 b5e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e114
          have b5e1064 : ∀ X0 X1 X2 X3 : G, (k X0 (τ (M.op X1 (M.op X2 X3)))) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e1051 X0 X1 X2 X3
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1051
            | exact resolve b5e1051 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1051
          have b5e2956 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e90 x y
               grind)
            | exact superpose b5e90 b5e24
            | (have j1 := b5e90 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e90 x y
               grind)
            | exact resolve b5e24 b5e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e3097 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b5e2956
          have b5e3106 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e3097
               have r₂ := b5e23
               grind)
            | exact resolve b5e3097 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3097
          have b5e3115 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e3106
               have i₂ := b5e81
               grind)
            | exact superpose b5e81 b5e3106
            | exact resolve b5e3106 b5e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81 b5e3106
          have b5e3132 : ∀ X0 : G, y ≠ (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e60 X0 (σ x) (σ y)
               have i₂ := b5e3115
               grind)
            | exact superpose b5e3115 b5e60
            | exact resolve b5e60 b5e3115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e3149 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ y)))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1064 X0 X1 (σ x) (σ y)
               have i₂ := b5e3115
               grind)
            | exact superpose b5e3115 b5e1064
            | exact resolve b5e1064 b5e3115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1064
          have b5e3260 : y ≠ (σ y) := by
            first
            | (have i₁ := b5e3132 (σ x)
               have i₂ := b5e3115
               grind)
            | exact superpose b5e3115 b5e3132
            | exact resolve b5e3132 b5e3115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3132
          have b5e4157 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
            intro X0
            first
            | (have i₁ := b5e176 X0 (M.op (σ x) (σ y))
               have i₂ := b5e898 (σ X0)
               grind)
            | exact superpose b5e898 b5e176
            | exact resolve b5e176 b5e898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e176 b5e898
          have b5e4160 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4157 X0
               have i₂ := b5e3149 X0 (σ x)
               grind)
            | exact superpose b5e3149 b5e4157
            | exact resolve b5e4157 b5e3149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3149 b5e4157
          have b5e4167 : ∀ X0 : G, (τ (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4160 X0
               have i₂ := b5e3115
               grind)
            | exact superpose b5e3115 b5e4160
            | exact resolve b5e4160 b5e3115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3115 b5e4160
          have b5e4173 : ∀ X0 : G, y = X0 := by
            intro X0
            first
            | (have i₁ := b5e4167 X0
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e4167
            | exact resolve b5e4167 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4167
          have b5e4329 : y ≠ y := by
            first
            | (have i₁ := b5e3260
               have i₂ := b5e4173 (σ y)
               grind)
            | exact superpose b5e4173 b5e3260
            | (have r₁ := b5e3260
               have r₂ := b5e4173 (σ y)
               grind)
            | exact resolve b5e3260 b5e4173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3260 b5e4173
          have b5e4386 : False := by grind
          exact b5e4386
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e30 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) x (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ y)
             have i₂ := b6e30 X0
             grind)
          | exact superpose b6e30 b6e12
          | exact resolve b6e12 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e45 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e44 X0 x
             have i₂ := b6e30 x
             grind)
          | exact superpose b6e30 b6e44
          | exact resolve b6e44 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e44
        have b6e50 : y ≠ (σ y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e45 x
             grind)
          | exact superpose b6e45 b6e20
          | exact resolve b6e20 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          grind
        have b6e99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e16 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X0 X1
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 (M.op X0 X1)
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e99 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e106 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e105 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e105
        have b6e110 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (σ y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e106 X0 X1
             have i₂ := b6e45 X0
             grind)
          | exact superpose b6e45 b6e106
          | (have j0 := b6e106 X0 X1
             grind)
          | exact resolve b6e106 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e247 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e52 (σ X0)
             grind)
          | exact superpose b6e52 b6e18
          | exact resolve b6e18 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e817 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e247 X0
             grind)
          | exact superpose b6e247 b6e13
          | exact resolve b6e13 b6e247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e247
        have b6e818 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e817 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e817
          | exact resolve b6e817 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e817
        have b6e853 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e110 X0 y
             have i₂ := b6e818 X0
             grind)
          | exact superpose b6e818 b6e110
          | (have j0 := b6e110 X0 y
             grind)
          | exact resolve b6e110 b6e818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110
        have b6e858 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e853 X0
             grind)
          | (have r₁ := b6e853 (σ y)
             have r₂ := b6e50
             grind)
          | (have r₁ := b6e853 X0
             have r₂ := b6e50
             grind)
          | exact resolve b6e853 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e853
        have b6e1599 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = y ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e16 X0 y
             have i₂ := b6e858 X0
             grind)
          | exact superpose b6e858 b6e16
          | (have j0 := b6e16 X0 y
             have j1 := b6e858 (M.op X0 X0)
             grind)
          | exact resolve b6e16 b6e858
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e858
        have b6e1622 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = y ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e1599 X0
             have i₂ := b6e45 X0
             grind)
          | exact superpose b6e45 b6e1599
          | (have j0 := b6e1599 X0
             grind)
          | (have r₁ := b6e1599 (σ y)
             have r₂ := b6e45 (σ y)
             grind)
          | exact resolve b6e1599 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1599
        have b6e1625 : ∀ X0 : G, y = (σ y) ∨ (σ y) ≠ X0 ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e1622 X0
             have i₂ := b6e45 X0
             grind)
          | exact superpose b6e45 b6e1622
          | (have j0 := b6e1622 X0
             grind)
          | (have r₁ := b6e1622 (M.op X0 X0)
             have r₂ := b6e45 X0
             grind)
          | exact resolve b6e1622 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45 b6e1622
        have b6e1627 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e1625 X0
             grind)
          | (have r₁ := b6e1625 X0
             have r₂ := b6e50
             grind)
          | (have r₁ := b6e1625 (σ y)
             have r₂ := b6e50
             grind)
          | exact resolve b6e1625 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1625
        have b6e1628 : ∀ X0 : G, y = X0 ∨ (σ y) ≠ X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e1627 X0
             have i₂ := b6e818 X0
             grind)
          | exact superpose b6e818 b6e1627
          | (have j0 := b6e1627 X0
             grind)
          | (have r₁ := b6e1627 (k (σ y) y)
             have r₂ := b6e818 (σ y)
             grind)
          | exact resolve b6e1627 b6e818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e818 b6e1627
        have b6e1629 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e1628 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1628
        have b6e1660 : y = (σ y) := by
          first
          | (have j0 := b6e1629 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1629
        have b6e1661 : False := by grind
        exact b6e1661
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
          have b7e30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e30 X1 X0 x
               have i₂ := b7e13 X1 x X1
               grind)
            | (have i₁ := b7e30 X0 X1 (M.op X0 X0)
               have i₂ := b7e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e51 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e34 x X0
               grind)
            | (have i₁ := b7e21
               have i₂ := b7e34 X0 x
               grind)
            | exact superpose b7e34 b7e21
            | exact resolve b7e21 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e61 : ∀ X0 X1 X2 : G, y ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e51 X1
               have i₂ := b7e13 X1 X0 X2
               grind)
            | exact superpose b7e13 b7e51
            | exact resolve b7e51 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e76 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e78 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e76
          have b7e82 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e78
               have r₂ := b7e23
               grind)
            | exact resolve b7e78 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e84 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e82
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e82
            | exact resolve b7e82 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e87 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e84
               grind)
            | exact superpose b7e84 b7e14
            | exact resolve b7e14 b7e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e88 : y = (k x y) := by
            first
            | (have i₁ := b7e87
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e87
            | exact resolve b7e87 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e123 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e88
               grind)
            | exact superpose b7e88 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e124 : y = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e123
               have r₂ := b7e22
               grind)
            | exact resolve b7e123 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e123
          have b7e126 : y = (M.op x y) := by
            first
            | (have r₁ := b7e124
               have r₂ := b7e21
               grind)
            | exact resolve b7e124 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e124
          have b7e201 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e61 X0 x y
               have i₂ := b7e126
               grind)
            | exact superpose b7e126 b7e61
            | exact resolve b7e61 b7e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e291 : y ≠ y := by
            first
            | (have i₁ := b7e201 x
               have i₂ := b7e126
               grind)
            | exact superpose b7e126 b7e201
            | (have r₁ := b7e201 x
               have r₂ := b7e126
               grind)
            | exact resolve b7e201 b7e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126 b7e201
          have b7e292 : False := by grind
          exact b7e292
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
          have b8e90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b8e2875 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e90 x y
               grind)
            | exact superpose b8e90 b8e24
            | (have j1 := b8e90 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e90 x y
               grind)
            | exact resolve b8e24 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e3012 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b8e2875
          have b8e3022 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e3012
               have r₂ := b8e23
               grind)
            | exact resolve b8e3012 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3012
          have b8e3033 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3022
               grind)
            | exact superpose b8e3022 b8e20
            | exact resolve b8e20 b8e3022
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3022
          have b8e3818 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e3033
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e3033
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e3033 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3033
          have b8e3827 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
          clear b8e3818
          have b8e3831 : y = (M.op x x) := by
            first
            | (have r₁ := b8e3827
               have r₂ := b8e22
               grind)
            | exact resolve b8e3827 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3827
          have b8e3832 : False := by grind
          exact b8e3832

/-- `Equation314`: `x ◇ x = y ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyy_x_y_pxy_Equation314 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law314 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law314.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, y = (M.op X0 y) := by
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
      have b0e38 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e11
        | exact resolve b0e11 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e38 X0 x
           have i₂ := b0e27 x
           grind)
        | exact superpose b0e27 b0e38
        | exact resolve b0e38 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e72 : y = (σ y) := by
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
      have b0e166 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e72
           grind)
        | exact superpose b0e72 b0e18
        | exact resolve b0e18 b0e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e171 : y ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e166
           have i₂ := b0e27 (σ x)
           grind)
        | exact superpose b0e27 b0e166
        | exact resolve b0e166 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e166
      have b0e172 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e171
           have i₂ := b0e27 x
           grind)
        | exact superpose b0e27 b0e171
        | exact resolve b0e171 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e171
      have b0e173 : False := by grind
      exact b0e173
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : ∀ X0 : G, y = (M.op X0 y) := by
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
        have b1e34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e37 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 y
             have i₂ := b1e27 X0
             grind)
          | exact superpose b1e27 b1e12
          | exact resolve b1e12 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, (M.op X0 X0) = y := by
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
        have b1e40 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) x (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e40 x
             have i₂ := b1e12 (σ x) x (σ y)
             grind)
          | (have i₁ := b1e40 (M.op (σ x) (σ y))
             have i₂ := b1e12 (M.op (σ x) (σ y)) x x
             grind)
          | exact superpose b1e12 b1e40
          | exact resolve b1e40 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e42 : y = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e38 (σ x)
             grind)
          | exact superpose b1e38 b1e41
          | exact resolve b1e41 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e47 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          grind
        have b1e50 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e38 (σ x)
             grind)
          | exact superpose b1e38 b1e21
          | exact resolve b1e21 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e59 : ∀ X0 X1 : G, (M.op X0 X1) ≠ y ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e38 X1
             grind)
          | exact superpose b1e38 b1e16
          | (have j0 := b1e16 X0 X1
             grind)
          | exact resolve b1e16 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 X1 : G, y = X1 ∨ (M.op X0 X1) ≠ y ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e59 X0 X1
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e59
          | (have j0 := b1e59 X0 X1
             grind)
          | (have r₁ := b1e59 X0 X0
             have r₂ := b1e38 X0
             grind)
          | exact resolve b1e59 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e89 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X2) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e17 X0 X1
             have i₂ := b1e17 X2 X1
             grind)
          | (have i₁ := b1e17 X0 X1
             have i₂ := b1e17 X1 X1
             grind)
          | exact superpose b1e17 b1e17
          | (have j0 := b1e17 X2 X1
             have j1 := b1e17 X2 X1
             grind)
          | exact resolve b1e17 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e109 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X2) = X1 ∨ (k X2 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X2 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e17 X1 X1
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X2 X1
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X0 X0
             have r₂ := b1e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b1e16 X0 X0
             have r₂ := b1e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e132 : ∀ X0 X1 X2 : G, y = X1 ∨ (M.op X0 X1) ≠ (M.op X2 X1) ∨ (k X2 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e109 X0 X1 X2
             have i₂ := b1e38 X2
             grind)
          | exact superpose b1e38 b1e109
          | (have j0 := b1e109 X0 X1 X2
             grind)
          | exact resolve b1e109 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e109
        have b1e149 : ∀ X0 X1 X2 : G, y = X1 ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e89 X0 X1 X2
             have i₂ := b1e38 X2
             grind)
          | exact superpose b1e38 b1e89
          | (have j0 := b1e89 X0 X1 X2
             grind)
          | exact resolve b1e89 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89
        have b1e160 : ∀ X0 X1 X2 : G, y = X1 ∨ y = X1 ∨ (M.op X0 X1) ≠ (M.op X2 X1) ∨ (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e132 X0 X1 X2
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e132
          | (have j0 := b1e132 X0 X1 X2
             grind)
          | exact resolve b1e132 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e132
        have b1e161 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ y = X1 ∨ (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e160 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160
        have b1e170 : ∀ X0 X1 X2 : G, y = X1 ∨ y = X1 ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e149 X0 X1 X2
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e149
          | (have j0 := b1e149 X0 X1 X2
             grind)
          | exact resolve b1e149 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e149
        have b1e171 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ y = X1 := by
          intro X0 X1 X2
          first
          | (have j0 := b1e170 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e170
        have b1e352 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e34 X0 y
             have i₂ := b1e47 (τ X0)
             grind)
          | exact superpose b1e47 b1e34
          | exact resolve b1e34 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e356 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e352 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e352
          | exact resolve b1e352 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e352
        have b1e1581 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ y = (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e161 (σ y) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e161
          | (have j0 := b1e161 (σ x) (σ y) X0
             grind)
          | (have r₁ := b1e161 (σ x) (σ y) (σ y)
             have r₂ := b1e22
             grind)
          | (have r₁ := b1e161 (σ y) (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e161 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e161
        have b1e1609 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b1e1581 X0
             grind)
          | (have r₁ := b1e1581 X0
             have r₂ := b1e50
             grind)
          | exact resolve b1e1581 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1581
        have b1e1618 : ∀ X0 : G, y ≠ (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1609 X0
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e1609
          | (have j0 := b1e1609 X0
             grind)
          | exact resolve b1e1609 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1609
        have b1e1620 : ∀ X0 : G, (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1618 X0
             have i₂ := b1e356 X0
             grind)
          | exact superpose b1e356 b1e1618
          | (have j0 := b1e1618 X0
             grind)
          | exact resolve b1e1618 b1e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1618
        have b1e1622 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1620 X0
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e1620
          | (have j0 := b1e1620 X0
             grind)
          | exact resolve b1e1620 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1620
        have b1e1624 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1622 X0
             have i₂ := b1e47 y
             grind)
          | exact superpose b1e47 b1e1622
          | (have j0 := b1e1622 X0
             grind)
          | exact resolve b1e1622 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1622
        have b1e1625 : ∀ X0 : G, y = (σ y) ∨ (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1624 X0
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e1624
          | (have j0 := b1e1624 X0
             grind)
          | (have r₁ := b1e1624 (σ x)
             have r₂ := b1e42
             grind)
          | exact resolve b1e1624 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1624
        have b1e1626 : ∀ X0 : G, y ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b1e1625 X0
             grind)
          | (have r₁ := b1e1625 X0
             have r₂ := b1e50
             grind)
          | (have r₁ := b1e1625 y
             have r₂ := b1e50
             grind)
          | exact resolve b1e1625 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1625
        have b1e1629 : y ≠ y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1626 (σ x)
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e1626
          | (have j0 := b1e1626 (σ x)
             grind)
          | (have r₁ := b1e1626 (σ x)
             have r₂ := b1e42
             grind)
          | exact resolve b1e1626 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1626
        have b1e1631 : (σ x) = (σ y) := by grind
        clear b1e1629
        have b1e1721 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e171 X0 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e171
          | (have j0 := b1e171 X0 (σ y) X0
             grind)
          | exact resolve b1e171 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e171
        have b1e1958 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b1e1721 X0
             grind)
          | (have r₁ := b1e1721 X0
             have r₂ := b1e50
             grind)
          | exact resolve b1e1721 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1721
        have b1e2034 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1958 X0
             have i₂ := b1e1631
             grind)
          | exact superpose b1e1631 b1e1958
          | (have j0 := b1e1958 X0
             grind)
          | exact resolve b1e1958 b1e1631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1958
        have b1e2070 : ∀ X0 : G, y = (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e2034 X0
             have i₂ := b1e38 (σ x)
             grind)
          | exact superpose b1e38 b1e2034
          | (have j0 := b1e2034 X0
             grind)
          | exact resolve b1e2034 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2034
        have b1e2094 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e2070 X0
             have i₂ := b1e356 X0
             grind)
          | exact superpose b1e356 b1e2070
          | (have j0 := b1e2070 X0
             grind)
          | exact resolve b1e2070 b1e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2070
        have b1e2118 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ y = (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e2094 X0
             have i₂ := b1e1631
             grind)
          | exact superpose b1e1631 b1e2094
          | (have j0 := b1e2094 X0
             grind)
          | exact resolve b1e2094 b1e1631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2094
        have b1e2134 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op X0 (σ x)) = X0 ∨ y = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e2118 X0
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e2118
          | (have j0 := b1e2118 X0
             grind)
          | exact resolve b1e2118 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2118
        have b1e2142 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = X0 ∨ y = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e2134 X0
             have i₂ := b1e47 y
             grind)
          | exact superpose b1e47 b1e2134
          | (have j0 := b1e2134 X0
             grind)
          | exact resolve b1e2134 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e2134
        have b1e2148 : ∀ X0 : G, y = (σ y) ∨ (M.op X0 (σ x)) = X0 ∨ y = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e2142 X0
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e2142
          | (have j0 := b1e2142 X0
             grind)
          | exact resolve b1e2142 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e2142
        have b1e2154 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ y = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e2148 X0
             grind)
          | (have r₁ := b1e2148 X0
             have r₂ := b1e50
             grind)
          | exact resolve b1e2148 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2148
        have b1e2161 : y ≠ (σ x) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e1631
             grind)
          | exact superpose b1e1631 b1e50
          | exact resolve b1e50 b1e1631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2163 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e356 X0
             have i₂ := b1e1631
             grind)
          | exact superpose b1e1631 b1e356
          | exact resolve b1e356 b1e1631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e356
        have b1e2168 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e1631
             grind)
          | exact superpose b1e1631 b1e13
          | exact resolve b1e13 b1e1631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1631
        have b1e2180 : x = y := by
          first
          | (have i₁ := b1e2168
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e2168
          | exact resolve b1e2168 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2168
        have b1e2227 : x ≠ (σ x) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e2180
             grind)
          | exact superpose b1e2180 b1e50
          | exact resolve b1e50 b1e2180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e3116 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ x)
             have i₂ := b1e2154 X0
             grind)
          | exact superpose b1e2154 b1e16
          | (have j0 := b1e16 X0 (σ x)
             have j1 := b1e2154 X0
             grind)
          | (have r₁ := b1e16 (M.op (σ x) (σ x)) (σ x)
             have r₂ := b1e2154 (M.op (σ x) (σ x))
             grind)
          | exact resolve b1e16 b1e2154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2154
        have b1e3179 : ∀ X0 : G, y ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e3116 X0
             have i₂ := b1e38 (σ x)
             grind)
          | exact superpose b1e38 b1e3116
          | (have j0 := b1e3116 X0
             grind)
          | (have r₁ := b1e3116 y
             have r₂ := b1e38 (σ x)
             grind)
          | exact resolve b1e3116 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3116
        have b1e3195 : ∀ X0 : G, x ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e3179 X0
             have i₂ := b1e2180
             grind)
          | exact superpose b1e2180 b1e3179
          | (have j0 := b1e3179 X0
             grind)
          | (have r₁ := b1e3179 x
             have r₂ := b1e2180
             grind)
          | exact resolve b1e3179 b1e2180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2180 b1e3179
        have b1e3208 : ∀ X0 : G, y = (σ x) ∨ x ≠ X0 ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e3195 X0
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e3195
          | (have j0 := b1e3195 X0
             grind)
          | exact resolve b1e3195 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e3195
        have b1e3217 : ∀ X0 : G, y = (σ x) ∨ x ≠ X0 ∨ (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e3208 X0
             have j1 := b1e73 X0 (σ x)
             grind)
          | (have r₁ := b1e3208 y
             have r₂ := b1e73 X0 x
             grind)
          | (have r₁ := b1e3208 (k X0 x)
             have r₂ := b1e73 X0 x
             grind)
          | (have r₁ := b1e3208 X0
             have r₂ := b1e73 X0 (σ x)
             grind)
          | exact resolve b1e3208 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73 b1e3208
        have b1e3220 : ∀ X0 : G, x ≠ X0 ∨ (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e3217 X0
             grind)
          | (have r₁ := b1e3217 X0
             have r₂ := b1e2161
             grind)
          | exact resolve b1e3217 b1e2161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2161 b1e3217
        have b1e3221 : ∀ X0 : G, x ≠ X0 ∨ (σ x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e3220 X0
             have i₂ := b1e2163 X0
             grind)
          | exact superpose b1e2163 b1e3220
          | (have j0 := b1e3220 X0
             grind)
          | (have r₁ := b1e3220 (k x (σ x))
             have r₂ := b1e2163 x
             grind)
          | exact resolve b1e3220 b1e2163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2163 b1e3220
        have b1e4041 : x = (σ x) := by
          first
          | (have j0 := b1e3221 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3221
        have b1e4042 : False := by grind
        exact b1e4042
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 : G, y = (M.op X0 y) := by
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
        have b2e34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e37 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 y
             have i₂ := b2e27 X0
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b2e37 X0 x
             have i₂ := b2e27 x
             grind)
          | exact superpose b2e27 b2e37
          | exact resolve b2e37 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e37
        have b2e42 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          grind
        have b2e45 : y ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e38 (σ x)
             grind)
          | exact superpose b2e38 b2e21
          | exact resolve b2e21 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e16 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e93 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e109 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e108 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108
        have b2e121 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ y = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e109 X0 X1
             have i₂ := b2e38 X1
             grind)
          | exact superpose b2e38 b2e109
          | (have j0 := b2e109 X0 X1
             grind)
          | exact resolve b2e109 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109
        have b2e319 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e34 X0 y
             have i₂ := b2e42 (τ X0)
             grind)
          | exact superpose b2e42 b2e34
          | exact resolve b2e34 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e42
        have b2e323 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e319 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e319
          | exact resolve b2e319 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e319
        have b2e923 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e121 (σ y) X0
             have i₂ := b2e323 X0
             grind)
          | exact superpose b2e323 b2e121
          | (have j0 := b2e121 (σ y) x
             grind)
          | exact resolve b2e121 b2e323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121
        have b2e951 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b2e923 X0
             grind)
          | (have r₁ := b2e923 y
             have r₂ := b2e45
             grind)
          | (have r₁ := b2e923 X0
             have r₂ := b2e45
             grind)
          | exact resolve b2e923 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e923
        have b2e2412 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 X0 (σ y)
             have i₂ := b2e951 X0
             grind)
          | exact superpose b2e951 b2e16
          | (have j0 := b2e16 X0 (σ y)
             have j1 := b2e951 (M.op X0 X0)
             grind)
          | (have r₁ := b2e16 (M.op (σ y) (σ y)) (σ y)
             have r₂ := b2e951 (M.op (σ y) (σ y))
             grind)
          | exact resolve b2e16 b2e951
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e951
        have b2e2447 : ∀ X0 : G, y ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e2412 X0
             have i₂ := b2e38 (σ y)
             grind)
          | exact superpose b2e38 b2e2412
          | (have j0 := b2e2412 X0
             grind)
          | (have r₁ := b2e2412 y
             have r₂ := b2e38 (σ y)
             grind)
          | exact resolve b2e2412 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2412
        have b2e2461 : ∀ X0 : G, y = (σ y) ∨ y ≠ X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e2447 X0
             have i₂ := b2e38 X0
             grind)
          | exact superpose b2e38 b2e2447
          | (have j0 := b2e2447 X0
             grind)
          | (have r₁ := b2e2447 (M.op X0 X0)
             have r₂ := b2e38 X0
             grind)
          | exact resolve b2e2447 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e2447
        have b2e2467 : ∀ X0 : G, y ≠ X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b2e2461 X0
             grind)
          | (have r₁ := b2e2461 X0
             have r₂ := b2e45
             grind)
          | (have r₁ := b2e2461 y
             have r₂ := b2e45
             grind)
          | exact resolve b2e2461 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2461
        have b2e2470 : ∀ X0 : G, (σ y) = X0 ∨ y ≠ X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e2467 X0
             have i₂ := b2e323 X0
             grind)
          | exact superpose b2e323 b2e2467
          | (have j0 := b2e2467 X0
             grind)
          | (have r₁ := b2e2467 (k y (σ y))
             have r₂ := b2e323 y
             grind)
          | exact resolve b2e2467 b2e323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e323 b2e2467
        have b2e2471 : ∀ X0 : G, y ≠ X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b2e2470 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2470
        have b2e2583 : y = (σ y) := by
          first
          | (have j0 := b2e2471 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2471
        have b2e2584 : False := by grind
        exact b2e2584
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e29 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b3e12 y x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) x (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b3e29 x
             have i₂ := b3e12 x x y
             grind)
          | (have i₁ := b3e29 (M.op x y)
             have i₂ := b3e12 (M.op x y) x x
             grind)
          | exact superpose b3e12 b3e29
          | exact resolve b3e29 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e47 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (σ y)
             have i₂ := b3e30 X0
             grind)
          | exact superpose b3e30 b3e12
          | exact resolve b3e12 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e47 X0 x
             have i₂ := b3e30 x
             grind)
          | exact superpose b3e30 b3e47
          | exact resolve b3e47 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e47
        have b3e57 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = y ∨ y = (k X0 y) := by
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
        have b3e59 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X3 X1) ∨ (M.op X3 X3) = X1 ∨ (k X3 X1) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e16 X3 X1
             have i₂ := b3e12 X1 X0 X2
             grind)
          | exact superpose b3e12 b3e16
          | (have j0 := b3e16 X3 X1
             grind)
          | exact resolve b3e16 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e68 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X3 X1) ∨ (σ y) = X1 ∨ (k X3 X1) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e59 X0 X1 X2 X3
             have i₂ := b3e50 X3
             grind)
          | exact superpose b3e50 b3e59
          | (have j0 := b3e59 X0 X1 X2 X3
             grind)
          | exact resolve b3e59 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e70 : ∀ X0 : G, (M.op x x) ≠ (M.op X0 y) ∨ (M.op X0 X0) = y ∨ y = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e57 X0
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e57
          | (have j0 := b3e57 X0
             grind)
          | exact resolve b3e57 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e57
        have b3e75 : ∀ X0 : G, (σ y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = y ∨ y = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e70 X0
             have i₂ := b3e50 x
             grind)
          | exact superpose b3e50 b3e70
          | (have j0 := b3e70 X0
             grind)
          | exact resolve b3e70 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e78 : ∀ X0 : G, (σ y) ≠ (M.op X0 y) ∨ y = (σ y) ∨ y = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e75 X0
             have i₂ := b3e50 X0
             grind)
          | exact superpose b3e50 b3e75
          | (have j0 := b3e75 X0
             grind)
          | (have r₁ := b3e75 y
             have r₂ := b3e50 y
             grind)
          | exact resolve b3e75 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 X0
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e16 X1 X1
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X1 X0
             have j1 := b3e17 X1 X0
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e119 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e103 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e120 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e119 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119
        have b3e130 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (σ y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e120 X0 X1
             have i₂ := b3e50 X1
             grind)
          | exact superpose b3e50 b3e120
          | (have j0 := b3e120 X0 X1
             grind)
          | exact resolve b3e120 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120
        have b3e171 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          grind
        have b3e175 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e50 x
             grind)
          | exact superpose b3e50 b3e20
          | exact resolve b3e20 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e176 : (M.op x y) = (σ y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e50 y
             grind)
          | exact superpose b3e50 b3e21
          | exact resolve b3e21 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e270 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e171 (σ X0)
             grind)
          | exact superpose b3e171 b3e18
          | exact resolve b3e18 b3e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e517 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e270 X0
             grind)
          | exact superpose b3e270 b3e13
          | exact resolve b3e13 b3e270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e270
        have b3e518 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e517 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e517
          | exact resolve b3e517 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e517
        have b3e1106 : (σ y) ≠ (σ y) ∨ y = (σ y) ∨ y = (k x y) := by
          first
          | (have i₁ := b3e78 x
             have i₂ := b3e176
             grind)
          | exact superpose b3e176 b3e78
          | (have j0 := b3e78 x
             grind)
          | (have r₁ := b3e78 x
             have r₂ := b3e176
             grind)
          | exact resolve b3e78 b3e176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78 b3e176
        have b3e1109 : y = (σ y) ∨ y = (k x y) := by grind
        clear b3e1106
        have b3e1112 : y = (k x y) := by
          first
          | (have r₁ := b3e1109
             have r₂ := b3e175
             grind)
          | exact resolve b3e1109 b3e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1109
        have b3e1114 : x = y := by
          first
          | (have i₁ := b3e1112
             have i₂ := b3e518 x
             grind)
          | exact superpose b3e518 b3e1112
          | exact resolve b3e1112 b3e518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1112
        have b3e1125 : x ≠ (σ x) := by
          first
          | (have i₁ := b3e175
             have i₂ := b3e1114
             grind)
          | exact superpose b3e1114 b3e175
          | exact resolve b3e175 b3e1114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1130 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e518 X0
             have i₂ := b3e1114
             grind)
          | exact superpose b3e1114 b3e518
          | exact resolve b3e518 b3e1114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1149 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e130 y X0
             have i₂ := b3e518 X0
             grind)
          | exact superpose b3e518 b3e130
          | (have j0 := b3e130 y x
             grind)
          | exact resolve b3e130 b3e518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130 b3e518
        have b3e1185 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e1149 X0
             grind)
          | (have r₁ := b3e1149 (σ y)
             have r₂ := b3e175
             grind)
          | (have r₁ := b3e1149 X0
             have r₂ := b3e175
             grind)
          | exact resolve b3e1149 b3e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e175 b3e1149
        have b3e1198 : ∀ X0 : G, (M.op X0 x) = X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e1185 X0
             have i₂ := b3e1114
             grind)
          | exact superpose b3e1114 b3e1185
          | (have j0 := b3e1185 X0
             grind)
          | exact resolve b3e1185 b3e1114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1185
        have b3e1209 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e1198 X0
             have i₂ := b3e1114
             grind)
          | exact superpose b3e1114 b3e1198
          | (have j0 := b3e1198 X0
             grind)
          | exact resolve b3e1198 b3e1114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1198
        have b3e2333 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X2)) ≠ X0 ∨ x = (σ y) ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e68 X1 x X2 X0
             have i₂ := b3e1209 X0
             grind)
          | exact superpose b3e1209 b3e68
          | (have j0 := b3e68 X0 x X2 X0
             have j1 := b3e1209 (σ y)
             grind)
          | (have r₁ := b3e68 X0 x X2 (M.op X0 (M.op x X2))
             have r₂ := b3e1209 (M.op X0 (M.op x X2))
             grind)
          | exact resolve b3e68 b3e1209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68 b3e1209
        have b3e2348 : ∀ X0 : G, (M.op x x) ≠ X0 ∨ x = (σ y) ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2333 X0 x x
             have i₂ := b3e12 x x x
             grind)
          | (have i₁ := b3e2333 X0 (M.op x x) x
             have i₂ := b3e12 (M.op x x) x x
             grind)
          | exact superpose b3e12 b3e2333
          | (have j0 := b3e2333 X0 x x
             grind)
          | (have r₁ := b3e2333 (M.op x (M.op (M.op x x) x)) (M.op x x) x
             have r₂ := b3e12 (M.op x x) x x
             grind)
          | (have r₁ := b3e2333 (M.op x x) x x
             have r₂ := b3e12 x x x
             grind)
          | exact resolve b3e2333 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2333
        have b3e2358 : ∀ X0 : G, (σ y) ≠ X0 ∨ x = (σ y) ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2348 X0
             have i₂ := b3e50 x
             grind)
          | exact superpose b3e50 b3e2348
          | (have j0 := b3e2348 X0
             grind)
          | (have r₁ := b3e2348 (σ y)
             have r₂ := b3e50 x
             grind)
          | exact resolve b3e2348 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e2348
        have b3e2366 : ∀ X0 : G, (σ x) ≠ X0 ∨ x = (σ y) ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2358 X0
             have i₂ := b3e1114
             grind)
          | exact superpose b3e1114 b3e2358
          | (have j0 := b3e2358 X0
             grind)
          | exact resolve b3e2358 b3e1114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2358
        have b3e2369 : ∀ X0 : G, x = (σ x) ∨ (σ x) ≠ X0 ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2366 X0
             have i₂ := b3e1114
             grind)
          | exact superpose b3e1114 b3e2366
          | (have j0 := b3e2366 X0
             grind)
          | exact resolve b3e2366 b3e1114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1114 b3e2366
        have b3e2372 : ∀ X0 : G, (σ x) ≠ X0 ∨ x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b3e2369 X0
             grind)
          | (have r₁ := b3e2369 X0
             have r₂ := b3e1125
             grind)
          | (have r₁ := b3e2369 (σ x)
             have r₂ := b3e1125
             grind)
          | exact resolve b3e2369 b3e1125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2369
        have b3e2374 : ∀ X0 : G, x = X0 ∨ (σ x) ≠ X0 ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e2372 X0
             have i₂ := b3e1130 X0
             grind)
          | exact superpose b3e1130 b3e2372
          | (have j0 := b3e2372 X0
             grind)
          | (have r₁ := b3e2372 (k (σ x) x)
             have r₂ := b3e1130 (σ x)
             grind)
          | exact resolve b3e2372 b3e1130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1130 b3e2372
        have b3e2375 : ∀ X0 : G, (σ x) ≠ X0 ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b3e2374 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2374
        have b3e2623 : x = (σ x) := by
          first
          | (have j0 := b3e2375 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2375
        have b3e2624 : False := by grind
        exact b3e2624
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
          have b4e32 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op X0 x)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0 x
               have i₂ := b4e13 X1 x X1
               grind)
            | (have i₁ := b4e32 X0 X1 (M.op X0 X0)
               have i₂ := b4e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e38 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e56 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            grind
          have b4e61 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e27
               have i₂ := b4e36 (σ y) X0
               grind)
            | (have i₁ := b4e27
               have i₂ := b4e36 X0 (σ y)
               grind)
            | exact superpose b4e36 b4e27
            | exact resolve b4e27 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e78 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X2) ∨ (M.op X1 X1) = X2 ∨ (k X1 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X1 X2
               have i₂ := b4e36 X2 X0
               grind)
            | (have i₁ := b4e17 X1 X2
               have i₂ := b4e36 X0 X2
               grind)
            | exact superpose b4e36 b4e17
            | (have j0 := b4e17 X1 X2
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e36 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e36 X0 X0
               grind)
            | exact resolve b4e17 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e119 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e137 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e119 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e119
          have b4e138 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e137 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137
          have b4e183 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X0 (M.op X1 X1)
               have i₂ := b4e56 X1 (τ X0)
               grind)
            | exact superpose b4e56 b4e38
            | exact resolve b4e38 b4e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e56
          have b4e190 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e183 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e183
            | exact resolve b4e183 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e183
          have b4e199 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e61 X1
               have i₂ := b4e36 y X0
               grind)
            | (have i₁ := b4e61 X1
               have i₂ := b4e36 X0 y
               grind)
            | exact superpose b4e36 b4e61
            | exact resolve b4e61 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e61
          have b4e964 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e138 (σ (M.op X1 X1)) X0
               have i₂ := b4e190 X0 X1
               grind)
            | exact superpose b4e190 b4e138
            | (have j0 := b4e138 (σ (M.op X1 X1)) X0
               grind)
            | exact resolve b4e138 b4e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138
          have b4e1055 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e964 X0 X1
               grind)
            | (have r₁ := b4e964 (σ (M.op X0 X0)) X0
               have r₂ := b4e199 X0 (σ (M.op X0 X0))
               grind)
            | (have r₁ := b4e964 X1 X0
               have r₂ := b4e199 X0 X1
               grind)
            | (have r₁ := b4e964 (M.op X1 X1) X0
               have r₂ := b4e199 X0 X1
               grind)
            | exact resolve b4e964 b4e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e964
          have b4e17274 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (σ (M.op X2 X2)) ∨ (σ (M.op X2 X2)) = (k X0 (σ (M.op X2 X2))) ∨ (σ (M.op X2 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e78 X1 X0 (σ (M.op X2 X2))
               have i₂ := b4e1055 X0 X2
               grind)
            | exact superpose b4e1055 b4e78
            | (have j0 := b4e78 X0 X0 (σ (M.op X2 X2))
               have j1 := b4e1055 (M.op X0 X0) X2
               grind)
            | (have r₁ := b4e78 X0 (M.op X0 X0) (σ (M.op X1 X1))
               have r₂ := b4e1055 (M.op X0 X0) X1
               grind)
            | exact resolve b4e78 b4e1055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78 b4e1055
          have b4e17366 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (σ (M.op X2 X2)) = (k X0 (σ (M.op X2 X2))) ∨ (σ (M.op X2 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e17274 X0 X1 X2
               grind)
            | (have r₁ := b4e17274 X1 X1 X0
               have r₂ := b4e199 X0 X1
               grind)
            | (have r₁ := b4e17274 (M.op X1 X1) X1 X0
               have r₂ := b4e199 X0 X1
               grind)
            | exact resolve b4e17274 b4e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17274
          have b4e17390 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (σ (M.op X2 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17366 X0 X1 X2
               have i₂ := b4e190 X0 X2
               grind)
            | exact superpose b4e190 b4e17366
            | (have j0 := b4e17366 X0 X1 X2
               grind)
            | (have r₁ := b4e17366 (k (M.op X1 X1) (σ (M.op X1 X1))) X1 X2
               have r₂ := b4e190 (M.op X1 X1) X1
               grind)
            | exact resolve b4e17366 b4e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e190 b4e17366
          have b4e17391 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (σ (M.op X2 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e17390 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17390
          have b4e18018 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e17391 (M.op X1 X1) X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17391
          have b4e18019 : False := by grind
          exact b4e18019
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e31 X1 X0 x
               have i₂ := b5e13 X1 x X1
               grind)
            | (have i₁ := b5e31 X0 X1 (M.op X0 X0)
               have i₂ := b5e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e58 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e35 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e35 X0 (σ x)
               grind)
            | exact superpose b5e35 b5e23
            | exact resolve b5e23 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e65 : ∀ X0 X1 X2 : G, (σ y) ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e58 X1
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e58
            | exact resolve b5e58 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e67 : (M.op y y) ≠ (M.op y y) ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e80 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e67
          have b5e83 : y = (k x y) := by
            first
            | (have r₁ := b5e80
               have r₂ := b5e21
               grind)
            | exact resolve b5e80 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e109 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b5e2052 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e109 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e109
          have b5e2053 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e2052
               have r₂ := b5e24
               grind)
            | exact resolve b5e2052 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2052
          have b5e2054 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2053
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2053
            | exact resolve b5e2053 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2053
          have b5e2055 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e2054
               have i₂ := b5e83
               grind)
            | exact superpose b5e83 b5e2054
            | exact resolve b5e2054 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e2054
          have b5e2069 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e65 X0 (σ x) (σ y)
               have i₂ := b5e2055
               grind)
            | exact superpose b5e2055 b5e65
            | exact resolve b5e65 b5e2055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e3408 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e2069 (σ x)
               have i₂ := b5e2055
               grind)
            | exact superpose b5e2055 b5e2069
            | (have r₁ := b5e2069 (σ x)
               have r₂ := b5e2055
               grind)
            | exact resolve b5e2069 b5e2055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2055 b5e2069
          have b5e3409 : False := by grind
          exact b5e3409
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e30 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) x (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ y)
             have i₂ := b6e30 X0
             grind)
          | exact superpose b6e30 b6e12
          | exact resolve b6e12 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e45 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e44 X0 x
             have i₂ := b6e30 x
             grind)
          | exact superpose b6e30 b6e44
          | exact resolve b6e44 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e44
        have b6e51 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          grind
        have b6e54 : y ≠ (σ y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e45 x
             grind)
          | exact superpose b6e45 b6e20
          | exact resolve b6e20 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e107 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e16 X1 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X1 X0
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e16 X0 X0
             have r₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b6e16 X0 X0
             have r₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e107 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e107
        have b6e125 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e124 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e124
        have b6e138 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (σ y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e125 X0 X1
             have i₂ := b6e45 X1
             grind)
          | exact superpose b6e45 b6e125
          | (have j0 := b6e125 X0 X1
             grind)
          | exact resolve b6e125 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e305 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e51 (σ X0)
             grind)
          | exact superpose b6e51 b6e18
          | exact resolve b6e18 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e931 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e305 X0
             grind)
          | exact superpose b6e305 b6e13
          | exact resolve b6e13 b6e305
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e305
        have b6e932 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e931 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e931
          | exact resolve b6e931 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e931
        have b6e1037 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e138 y X0
             have i₂ := b6e932 X0
             grind)
          | exact superpose b6e932 b6e138
          | (have j0 := b6e138 y x
             grind)
          | exact resolve b6e138 b6e932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e138
        have b6e1042 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e1037 X0
             grind)
          | (have r₁ := b6e1037 (σ y)
             have r₂ := b6e54
             grind)
          | (have r₁ := b6e1037 X0
             have r₂ := b6e54
             grind)
          | exact resolve b6e1037 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1037
        have b6e1377 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (M.op X0 X0) = y ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e16 X0 y
             have i₂ := b6e1042 X0
             grind)
          | exact superpose b6e1042 b6e16
          | (have j0 := b6e16 X0 y
             have j1 := b6e1042 (M.op X0 X0)
             grind)
          | (have r₁ := b6e16 (M.op y y) y
             have r₂ := b6e1042 (M.op y y)
             grind)
          | exact resolve b6e16 b6e1042
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1042
        have b6e1400 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = y ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e1377 X0
             have i₂ := b6e45 y
             grind)
          | exact superpose b6e45 b6e1377
          | (have j0 := b6e1377 X0
             grind)
          | (have r₁ := b6e1377 (σ y)
             have r₂ := b6e45 y
             grind)
          | exact resolve b6e1377 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1377
        have b6e1405 : ∀ X0 : G, y = (σ y) ∨ (σ y) ≠ X0 ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e1400 X0
             have i₂ := b6e45 X0
             grind)
          | exact superpose b6e45 b6e1400
          | (have j0 := b6e1400 X0
             grind)
          | (have r₁ := b6e1400 (M.op X0 X0)
             have r₂ := b6e45 X0
             grind)
          | exact resolve b6e1400 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45 b6e1400
        have b6e1407 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e1405 X0
             grind)
          | (have r₁ := b6e1405 X0
             have r₂ := b6e54
             grind)
          | (have r₁ := b6e1405 (σ y)
             have r₂ := b6e54
             grind)
          | exact resolve b6e1405 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1405
        have b6e1408 : ∀ X0 : G, y = X0 ∨ (σ y) ≠ X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e1407 X0
             have i₂ := b6e932 X0
             grind)
          | exact superpose b6e932 b6e1407
          | (have j0 := b6e1407 X0
             grind)
          | (have r₁ := b6e1407 (k (σ y) y)
             have r₂ := b6e932 (σ y)
             grind)
          | exact resolve b6e1407 b6e932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e932 b6e1407
        have b6e1409 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e1408 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1408
        have b6e1754 : y = (σ y) := by
          first
          | (have j0 := b6e1409 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1409
        have b6e1755 : False := by grind
        exact b6e1755
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e30 X1 X0 x
               have i₂ := b7e13 X1 x X1
               grind)
            | (have i₁ := b7e30 X0 X1 (M.op X0 X0)
               have i₂ := b7e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e51 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e34 x X0
               grind)
            | (have i₁ := b7e21
               have i₂ := b7e34 X0 x
               grind)
            | exact superpose b7e34 b7e21
            | exact resolve b7e21 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e61 : ∀ X0 X1 X2 : G, y ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e51 X1
               have i₂ := b7e13 X1 X0 X2
               grind)
            | exact superpose b7e13 b7e51
            | exact resolve b7e51 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e72 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e78 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e72
          have b7e83 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e78
               have r₂ := b7e23
               grind)
            | exact resolve b7e78 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e85 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e83
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e83
            | exact resolve b7e83 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e88 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e85
               grind)
            | exact superpose b7e85 b7e14
            | exact resolve b7e14 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e89 : y = (k x y) := by
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
          have b7e143 : y = (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e144 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e143
               have r₂ := b7e21
               grind)
            | exact resolve b7e143 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143
          have b7e146 : y = (M.op x y) := by
            first
            | (have r₁ := b7e144
               have r₂ := b7e22
               grind)
            | exact resolve b7e144 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e144
          have b7e221 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e61 X0 x y
               have i₂ := b7e146
               grind)
            | exact superpose b7e146 b7e61
            | exact resolve b7e61 b7e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e319 : y ≠ y := by
            first
            | (have i₁ := b7e221 x
               have i₂ := b7e146
               grind)
            | exact superpose b7e146 b7e221
            | (have r₁ := b7e221 x
               have r₂ := b7e146
               grind)
            | exact resolve b7e221 b7e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e146 b7e221
          have b7e320 : False := by grind
          exact b7e320
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e108 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e1657 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e108 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108
          have b8e1658 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1657
               have r₂ := b8e24
               grind)
            | exact resolve b8e1657 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1657
          have b8e1659 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1658
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1658
            | exact resolve b8e1658 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1658
          have b8e1663 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1659
               grind)
            | exact superpose b8e1659 b8e20
            | exact resolve b8e20 b8e1659
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1659
          have b8e2301 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1663
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1663
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1663 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1663
          have b8e2302 : y = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e2301
          have b8e2305 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e2302
               have r₂ := b8e21
               grind)
            | exact resolve b8e2302 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2302
          have b8e2308 : False := by grind
          exact b8e2308
