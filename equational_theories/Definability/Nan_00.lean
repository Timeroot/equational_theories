import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxx_pxx_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
      have b0e27 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 y x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
           have i₂ := b0e11 X0 X1 (M.op X0 (M.op X0 X1))
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op y y)
           have i₂ := b0e27 y
           grind)
        | exact superpose b0e27 b0e11
        | exact resolve b0e11 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X0 X1
           have i₂ := b0e16 X2 X0
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e16 X2 X0
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X1 X0
           have j1 := b0e16 X2 X0
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e15 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e55 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e61 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e59 X0 X2 X2
           have j1 := b0e14 X1 X0
           grind)
        | (have r₁ := b0e59 X1 X0 X2
           have r₂ := b0e14 X0 X1
           grind)
        | (have r₁ := b0e59 X1 X1 X0
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e59 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e83 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
           have i₂ := b0e11 X0 X1 (M.op X0 (M.op X0 X1))
           grind)
        | exact superpose b0e11 b0e34
        | exact resolve b0e34 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e105 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e83 (M.op X0 (M.op X0 X1)) y
           have i₂ := b0e34 X0 X1
           grind)
        | exact superpose b0e34 b0e83
        | exact resolve b0e83 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e34 X0 x
           have i₂ := b0e83 X0 x
           grind)
        | exact superpose b0e83 b0e34
        | exact resolve b0e34 b0e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e112 : ∀ X0 X2 : G, (M.op (M.op X0 y) (M.op X2 X2)) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b0e11 X0 x X2
           have i₂ := b0e83 X0 x
           grind)
        | exact superpose b0e83 b0e11
        | exact resolve b0e11 b0e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e118 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e105 X0 x
           have i₂ := b0e83 X0 x
           grind)
        | exact superpose b0e83 b0e105
        | exact resolve b0e105 b0e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105
      have b0e148 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e83 X0 x
           have i₂ := b0e30 X0 x X1
           grind)
        | (have i₁ := b0e83 x x
           have i₂ := b0e30 x X1 x
           grind)
        | exact superpose b0e30 b0e83
        | exact resolve b0e83 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e150 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X3 X3)) = X0 := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e11 X0 x X3
           have i₂ := b0e30 X0 x X1
           grind)
        | (have i₁ := b0e11 x x x
           have i₂ := b0e30 x X1 x
           grind)
        | exact superpose b0e30 b0e11
        | exact resolve b0e11 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e211 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e30 X0 X1 (M.op (σ y) (σ y))
           have i₂ := b0e28 (σ y)
           grind)
        | exact superpose b0e28 b0e30
        | exact resolve b0e30 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e30
      have b0e223 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e211 X0 x
           have i₂ := b0e83 X0 x
           grind)
        | exact superpose b0e83 b0e211
        | exact resolve b0e211 b0e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e211
      have b0e405 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e223 (σ x)
           grind)
        | exact superpose b0e223 b0e18
        | exact resolve b0e18 b0e223
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223
      have b0e460 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e61 X1 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e464 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e460 X0 X1
           have j1 := b0e14 X0 X1
           grind)
        | (have r₁ := b0e460 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e460 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e460
      have b0e528 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (M.op (σ X1) (σ X1)) (M.op X2 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e54 (σ X1) X2 (σ X0)
           grind)
        | exact superpose b0e54 b0e17
        | (have j1 := b0e54 (σ X1) X2 (σ X0)
           grind)
        | exact resolve b0e17 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e531 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) (σ X1)) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e528 X0 X1 x
           have i₂ := b0e148 (M.op (σ X1) (σ X1)) x
           grind)
        | exact superpose b0e148 b0e528
        | (have j0 := b0e528 X0 X1 x
           grind)
        | exact resolve b0e528 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e528
      have b0e1143 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op (M.op X0 X0) y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e148 X1 (M.op X0 X0)
           have i₂ := b0e148 (M.op X0 X0) X0
           grind)
        | exact superpose b0e148 b0e148
        | exact resolve b0e148 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1779 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e464 (M.op (M.op X1 X1) (M.op X1 X1)) X1
           have i₂ := b0e150 (M.op X1 X1) X1 (M.op X1 X1)
           grind)
        | exact superpose b0e150 b0e464
        | exact resolve b0e464 b0e150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e150
      have b0e1788 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e464 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e464
      have b0e1801 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) y) X1) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e1779 X0 X1
           have i₂ := b0e148 (M.op X0 X0) X0
           grind)
        | exact superpose b0e148 b0e1779
        | (have j0 := b0e1779 X0 X1
           grind)
        | exact resolve b0e1779 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1779
      have b0e1822 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) y) X1) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e1801 X0 X1
           have i₂ := b0e148 (M.op X0 X0) X0
           grind)
        | exact superpose b0e148 b0e1801
        | (have j0 := b0e1801 X0 X1
           grind)
        | exact resolve b0e1801 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1801
      have b0e1846 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e1788 (σ X0)
           grind)
        | exact superpose b0e1788 b0e17
        | exact resolve b0e17 b0e1788
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1848 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e21 X0 (τ X0)
           have i₂ := b0e1788 (τ X0)
           grind)
        | exact superpose b0e1788 b0e21
        | exact resolve b0e21 b0e1788
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e1849 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e1848 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e1848
        | exact resolve b0e1848 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1848
      have b0e1851 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e1846 X0
           have i₂ := b0e1788 X0
           grind)
        | exact superpose b0e1788 b0e1846
        | exact resolve b0e1846 b0e1788
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1846
      have b0e1855 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e1849 X0
           have i₂ := b0e1788 X0
           grind)
        | exact superpose b0e1788 b0e1849
        | exact resolve b0e1849 b0e1788
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1788 b0e1849
      have b0e3087 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e148 X1 (σ X0)
           have i₂ := b0e1851 X0
           grind)
        | exact superpose b0e1851 b0e148
        | exact resolve b0e148 b0e1851
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3818 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) y) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e1851 (M.op X0 X0)
           have i₂ := b0e3087 X0 (σ (M.op X0 X0))
           grind)
        | exact superpose b0e3087 b0e1851
        | exact resolve b0e1851 b0e3087
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3087
      have b0e3825 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) y) = (σ (M.op (M.op X0 X0) y)) := by
        intro X0
        first
        | (have i₁ := b0e3818 X0
           have i₂ := b0e148 (M.op X0 X0) X0
           grind)
        | exact superpose b0e148 b0e3818
        | exact resolve b0e3818 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148 b0e3818
      have b0e17913 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) y) ∨ (σ X0) = (M.op (M.op (σ X0) (σ X0)) y) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 (σ X0) (σ X1)
           have i₂ := b0e531 X1 X0
           grind)
        | exact superpose b0e531 b0e34
        | (have j1 := b0e531 X1 X0
           grind)
        | exact resolve b0e34 b0e531
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e531
      have b0e17921 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) y) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e17913 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e17913
      have b0e17932 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) y) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17921 X0 X1
           have i₂ := b0e1851 X0
           grind)
        | exact superpose b0e1851 b0e17921
        | (have j0 := b0e17921 X0 X1
           grind)
        | exact resolve b0e17921 b0e1851
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1851 b0e17921
      have b0e72623 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ (M.op (τ X0) (τ X0))) y) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e17932 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17932
        | exact resolve b0e17932 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e17932
      have b0e72852 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ (M.op (τ X0) (τ X0))) y) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e72623 X0 X1
           have i₂ := b0e22 X0 X1
           grind)
        | exact superpose b0e22 b0e72623
        | (have j0 := b0e72623 X0 X1
           grind)
        | exact resolve b0e72623 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e72623
      have b0e72980 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e72852 X0 X1
           have i₂ := b0e1855 X0
           grind)
        | exact superpose b0e1855 b0e72852
        | (have j0 := b0e72852 X0 X1
           grind)
        | exact resolve b0e72852 b0e1855
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1855 b0e72852
      have b0e113788 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) y) y) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) y) (M.op (M.op (M.op X0 X0) y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1822 X0 (M.op (M.op (M.op X0 X0) y) X1)
           have i₂ := b0e83 (M.op (M.op X0 X0) y) X1
           grind)
        | exact superpose b0e83 b0e1822
        | (have j0 := b0e1822 X0 y
           grind)
        | exact resolve b0e1822 b0e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83 b0e1822
      have b0e113889 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) y) (M.op (M.op (M.op X0 X0) y) X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e113788 X0 X1
           grind)
        | (have r₁ := b0e113788 X0 X1
           have r₂ := b0e111 (M.op X0 X0)
           grind)
        | exact resolve b0e113788 b0e111
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113788
      have b0e762720 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op (M.op X1 X1) y) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e72980 X0 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e72980
        | (have j0 := b0e72980 X1 X1
           grind)
        | exact resolve b0e72980 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72980
      have b0e762918 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 y) ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1143 X0 X1
           have i₂ := b0e762720 X2 X0
           grind)
        | exact superpose b0e762720 b0e1143
        | (have j1 := b0e762720 X2 X0
           grind)
        | exact resolve b0e1143 b0e762720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1143 b0e762720
      have b0e763147 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) (M.op X0 y)) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e112 X1 X0
           have i₂ := b0e762918 X0 X0 X2
           grind)
        | (have i₁ := b0e112 X0 y
           have i₂ := b0e762918 X0 y X2
           grind)
        | exact superpose b0e762918 b0e112
        | (have j1 := b0e762918 X0 X1 X2
           grind)
        | exact resolve b0e112 b0e762918
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112 b0e762918
      have b0e879412 : ∀ X0 X1 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e3825 (M.op X0 y)
           have i₂ := b0e763147 X0 X0 x
           grind)
        | exact superpose b0e763147 b0e3825
        | (have j1 := b0e763147 X0 X1 X1
           grind)
        | exact resolve b0e3825 b0e763147
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3825
      have b0e1041748 : ∀ X0 : G, (M.op (σ x) y) ≠ (M.op (σ x) y) ∨ (k X0 x) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e405
           have i₂ := b0e879412 x X0
           grind)
        | exact superpose b0e879412 b0e405
        | (have j1 := b0e879412 x X0
           grind)
        | (have r₁ := b0e405
           have r₂ := b0e879412 x x
           grind)
        | exact resolve b0e405 b0e879412
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e879412
      have b0e1041766 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b0e1041748 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1041748
      have b0e1210596 : ∀ X0 X1 X2 : G, (k (M.op X0 y) (M.op (M.op X0 y) X1)) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e113889 (M.op X0 y) X1
           have i₂ := b0e763147 X0 X0 X2
           grind)
        | exact superpose b0e763147 b0e113889
        | (have j1 := b0e763147 X0 X1 X2
           grind)
        | exact resolve b0e113889 b0e763147
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113889 b0e763147
      have b0e1396430 : ∀ X0 X1 : G, (k (M.op X0 y) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e1210596 X0 y X1
           have i₂ := b0e111 X0
           grind)
        | exact superpose b0e111 b0e1210596
        | (have j0 := b0e1210596 X0 X1 X1
           grind)
        | exact resolve b0e1210596 b0e111
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111 b0e1210596
      have b0e1396676 : ∀ X0 : G, (M.op (M.op X0 y) X0) ≠ X0 ∨ (k (M.op X0 y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e1396430 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1396430
      have b0e1396677 : ∀ X0 : G, (k (M.op X0 y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e1396676 X0
           grind)
        | (have r₁ := b0e1396676 X0
           have r₂ := b0e118 X0
           grind)
        | exact resolve b0e1396676 b0e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118 b0e1396676
      have b0e1397750 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e26 (M.op (σ X0) y) X0
           have i₂ := b0e1396677 (σ X0)
           grind)
        | exact superpose b0e1396677 b0e26
        | exact resolve b0e26 b0e1396677
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e1396677
      have b0e1397894 : ∀ X0 : G, (k (τ (M.op (σ X0) y)) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1397750 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1397750
        | exact resolve b0e1397750 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1397750
      have b0e1399780 : x = (M.op (τ (M.op (σ x) y)) x) := by
        first
        | (have i₁ := b0e1041766 (τ (M.op (σ x) y))
           have i₂ := b0e1397894 x
           grind)
        | exact superpose b0e1397894 b0e1041766
        | exact resolve b0e1041766 b0e1397894
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1041766 b0e1397894
      have b0e1400127 : (τ (M.op (σ x) y)) = (M.op (M.op (τ (M.op (σ x) y)) x) y) := by
        first
        | (have i₁ := b0e34 (τ (M.op (σ x) y)) x
           have i₂ := b0e1399780
           grind)
        | exact superpose b0e1399780 b0e34
        | exact resolve b0e34 b0e1399780
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e1400158 : (M.op x y) = (τ (M.op (σ x) y)) := by
        first
        | (have i₁ := b0e1400127
           have i₂ := b0e1399780
           grind)
        | exact superpose b0e1399780 b0e1400127
        | exact resolve b0e1400127 b0e1399780
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1399780 b0e1400127
      have b0e1400868 : (σ (M.op x y)) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e13 (M.op (σ x) y)
           have i₂ := b0e1400158
           grind)
        | exact superpose b0e1400158 b0e13
        | exact resolve b0e13 b0e1400158
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1400158
      have b0e1400897 : False := by grind
      exact b0e1400897
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
             have i₂ := b1e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (σ y)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e26 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e26
          | exact resolve b1e26 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e37 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have r₁ := b1e15 (σ y) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e37
        have b1e42 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e40
          | exact resolve b1e40 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e43 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 X0 (σ y)
             grind)
          | (have r₁ := b1e16 X0 (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e45 X0
             have j1 := b1e15 X0 (σ y)
             grind)
          | (have r₁ := b1e45 X0
             have r₂ := b1e15 X0 (σ y)
             grind)
          | exact resolve b1e45 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e50 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e13
          | exact resolve b1e13 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e51 : y = (k y y) := by
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
        have b1e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X1) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X1 X0
             have i₂ := b1e17 X2 X0
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X1 X0
             have j1 := b1e17 X2 X0
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b1e62 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e69 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b1e66 X0 X2 X2
             have j1 := b1e15 X1 X0
             grind)
          | (have r₁ := b1e66 X1 X0 X2
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e66 X1 X1 X0
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e66 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e71 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e72 : y = (M.op y y) := by grind
        clear b1e71
        have b1e86 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 y
             have i₂ := b1e47 (σ X0)
             grind)
          | exact superpose b1e47 b1e18
          | exact resolve b1e18 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e96 : ∀ X0 : G, y ≠ y ∨ y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 y
             have i₂ := b1e72
             grind)
          | exact superpose b1e72 b1e16
          | (have j0 := b1e16 X0 y
             grind)
          | (have r₁ := b1e16 X0 y
             have r₂ := b1e72
             grind)
          | exact resolve b1e16 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e99 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e96 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e96
        have b1e101 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e99 X0
             have j1 := b1e15 X0 y
             grind)
          | (have r₁ := b1e99 X0
             have r₂ := b1e15 X0 y
             grind)
          | exact resolve b1e99 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99
        have b1e157 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e29 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
             have i₂ := b1e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b1e12 b1e29
          | exact resolve b1e29 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e188 : ∀ X0 : G, (σ y) = (M.op (σ y) (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e30 X0
             have i₂ := b1e101 X0
             grind)
          | exact superpose b1e101 b1e30
          | exact resolve b1e30 b1e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e206 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e28 (M.op X0 (M.op X0 X1)) (M.op x x) X3
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e28
          | exact resolve b1e28 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e271 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e206 X0 X1 x
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e206
          | exact resolve b1e206 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e206
        have b1e276 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e271 X0 x
             have i₂ := b1e157 X0 x
             grind)
          | exact superpose b1e157 b1e271
          | exact resolve b1e271 b1e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e157 b1e271
        have b1e490 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e69 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e496 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e490 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e490 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e490 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e490
        have b1e1064 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e47 (σ X0)
             have i₂ := b1e57 X0 X0
             grind)
          | exact superpose b1e57 b1e47
          | (have j1 := b1e57 X0 X0
             grind)
          | exact resolve b1e47 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e1097 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e276 (σ X0)
             have i₂ := b1e57 y X0
             grind)
          | exact superpose b1e57 b1e276
          | (have j1 := b1e57 y X0
             grind)
          | exact resolve b1e276 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e276
        have b1e1110 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e1097 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1097
        have b1e1118 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e1064 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1064
        have b1e1142 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e1110 X0
             have i₂ := b1e86 X0
             grind)
          | exact superpose b1e86 b1e1110
          | (have j0 := b1e1110 X0
             grind)
          | exact resolve b1e1110 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1110
        have b1e1167 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e1118 X0
             have i₂ := b1e18 X0 y
             grind)
          | exact superpose b1e18 b1e1118
          | (have j0 := b1e1118 X0
             grind)
          | exact resolve b1e1118 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1118
        have b1e1216 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e1167 X0
             have i₂ := b1e86 X0
             grind)
          | exact superpose b1e86 b1e1167
          | (have j0 := b1e1167 X0
             grind)
          | exact resolve b1e1167 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1167
        have b1e1519 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ (k X0 y)) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e15 (σ X0) (σ X0)
             have i₂ := b1e86 X0
             grind)
          | exact superpose b1e86 b1e15
          | exact resolve b1e15 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86
        have b1e1533 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ X0) ≠ (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e1519 X0
             have i₂ := b1e18 X0 X0
             grind)
          | exact superpose b1e18 b1e1519
          | (have j0 := b1e1519 X0
             grind)
          | exact resolve b1e1519 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1519
        have b1e1552 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have j0 := b1e1533 X0
             have j1 := b1e1216 X0
             grind)
          | (have r₁ := b1e1533 X0
             have r₂ := b1e1216 X0
             grind)
          | exact resolve b1e1533 b1e1216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1216 b1e1533
        have b1e1942 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e1552 X0
             have i₂ := b1e101 X0
             grind)
          | exact superpose b1e101 b1e1552
          | exact resolve b1e1552 b1e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1974 : ∀ X0 : G, (k X0 X0) = (τ (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e13 (k X0 X0)
             have i₂ := b1e1552 X0
             grind)
          | (have i₁ := b1e13 (k X0 y)
             have i₂ := b1e1552 X0
             grind)
          | exact superpose b1e1552 b1e13
          | exact resolve b1e13 b1e1552
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1996 : ∀ X0 : G, (k X0 y) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e1974 X0
             have i₂ := b1e13 (k X0 y)
             grind)
          | exact superpose b1e13 b1e1974
          | exact resolve b1e1974 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1974
        have b1e2167 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e101 X0
             have i₂ := b1e1996 X0
             grind)
          | (have i₁ := b1e101 y
             have i₂ := b1e1996 y
             grind)
          | exact superpose b1e1996 b1e101
          | exact resolve b1e101 b1e1996
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e2186 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e1996 (σ X0)
             grind)
          | exact superpose b1e1996 b1e18
          | exact resolve b1e18 b1e1996
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1996
        have b1e2280 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e1552 X0
             have i₂ := b1e2167 X0
             grind)
          | exact superpose b1e2167 b1e1552
          | exact resolve b1e1552 b1e2167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1552 b1e2167
        have b1e4119 : y ≠ (M.op y y) ∨ (M.op y y) = (k y x) := by
          first
          | (have i₁ := b1e496 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e496
          | (have j0 := b1e496 y x
             grind)
          | exact resolve b1e496 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e496
        have b1e4157 : (M.op y y) = (k y x) := by
          first
          | (have r₁ := b1e4119
             have r₂ := b1e72
             grind)
          | exact resolve b1e4119 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4119
        have b1e4198 : y = (k y x) := by
          first
          | (have i₁ := b1e4157
             have i₂ := b1e72
             grind)
          | exact superpose b1e72 b1e4157
          | exact resolve b1e4157 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72 b1e4157
        have b1e5881 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (k X0 X0))) := by
          intro X0
          first
          | (have i₁ := b1e188 (σ X0)
             have i₂ := b1e2186 X0
             grind)
          | exact superpose b1e2186 b1e188
          | exact resolve b1e188 b1e2186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e188 b1e2186
        have b1e5895 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b1e5881 X0
             have i₂ := b1e1942 X0
             grind)
          | exact superpose b1e1942 b1e5881
          | exact resolve b1e5881 b1e1942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1942 b1e5881
        have b1e96031 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1142 x
             grind)
          | exact superpose b1e1142 b1e21
          | (have j1 := b1e1142 x
             grind)
          | exact resolve b1e21 b1e1142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1142
        have b1e96216 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e96031
             have i₂ := b1e4198
             grind)
          | exact superpose b1e4198 b1e96031
          | exact resolve b1e96031 b1e4198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4198 b1e96031
        have b1e96217 : (σ x) = (σ (k x y)) := by grind
        clear b1e96216
        have b1e96275 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e96217
             have i₂ := b1e2280 x
             grind)
          | exact superpose b1e2280 b1e96217
          | exact resolve b1e96217 b1e2280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2280 b1e96217
        have b1e96313 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e5895 x
             have i₂ := b1e96275
             grind)
          | exact superpose b1e96275 b1e5895
          | exact resolve b1e5895 b1e96275
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5895 b1e96275
        have b1e96498 : False := by grind
        exact b1e96498
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 y x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
             have i₂ := b2e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op y y)
             have i₂ := b2e25 y
             grind)
          | exact superpose b2e25 b2e12
          | exact resolve b2e12 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e45 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 X1 X0
             have i₂ := b2e17 X2 X0
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X1 X0
             have j1 := b2e17 X2 X0
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e47 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e55 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e53 X0 X2 X2
             have j1 := b2e15 X1 X0
             grind)
          | (have r₁ := b2e53 X1 X0 X2
             have r₂ := b2e15 X0 X1
             grind)
          | (have r₁ := b2e53 X1 X1 X0
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e53 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e73 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e31 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
             have i₂ := b2e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b2e12 b2e31
          | exact resolve b2e31 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e122 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X3 X0) = (k X3 X0) ∨ (M.op X0 X3) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e27 X1 X2 X0
             have i₂ := b2e17 X3 X0
             grind)
          | exact superpose b2e17 b2e27
          | (have j1 := b2e17 X3 X0
             grind)
          | exact resolve b2e27 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e129 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e73 X0 x
             have i₂ := b2e27 X0 x X1
             grind)
          | (have i₁ := b2e73 x x
             have i₂ := b2e27 x X1 x
             grind)
          | exact superpose b2e27 b2e73
          | exact resolve b2e73 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e155 : ∀ X0 X1 X3 : G, (M.op X3 X0) = (k X3 X0) ∨ (M.op X1 X0) = (M.op X1 y) ∨ (M.op X0 X3) = X0 := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e122 X0 X1 x X3
             have i₂ := b2e73 X1 x
             grind)
          | exact superpose b2e73 b2e122
          | (have j0 := b2e122 X0 X1 x X3
             grind)
          | exact resolve b2e122 b2e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122
        have b2e309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e54 (σ X1) (σ X0)
             grind)
          | exact superpose b2e54 b2e18
          | (have j1 := b2e54 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e325 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e309 X0 X1
             have i₂ := b2e18 X1 X1
             grind)
          | exact superpose b2e18 b2e309
          | (have j0 := b2e309 X0 X1
             grind)
          | exact resolve b2e309 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e309
        have b2e412 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e416 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e412 X0 X1
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e412 X0 X1
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e412 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412
        have b2e880 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X1 (σ X0)
             have i₂ := b2e43 X0 X0
             grind)
          | exact superpose b2e43 b2e16
          | (have j0 := b2e16 X1 (σ X0)
             have j1 := b2e43 X0 X0
             grind)
          | (have r₁ := b2e16 X0 (σ X1)
             have r₂ := b2e43 X0 X1
             grind)
          | (have r₁ := b2e16 X0 (σ X0)
             have r₂ := b2e43 X0 X0
             grind)
          | exact resolve b2e16 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e948 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e880 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e880
        have b2e975 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e948 X0 X1
             have j1 := b2e16 X1 (σ X0)
             grind)
          | (have r₁ := b2e948 X0 (σ X0)
             have r₂ := b2e16 X0 (σ X0)
             grind)
          | (have r₁ := b2e948 X0 X1
             have r₂ := b2e16 X0 (σ X0)
             grind)
          | exact resolve b2e948 b2e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e948
        have b2e986 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e975 X0 X1
             have j1 := b2e15 X1 (σ X0)
             grind)
          | (have r₁ := b2e975 X0 X0
             have r₂ := b2e15 X0 (σ X0)
             grind)
          | exact resolve b2e975 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e975
        have b2e1350 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e416 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e416
        have b2e1393 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e1350 (σ X0)
             grind)
          | exact superpose b2e1350 b2e18
          | exact resolve b2e18 b2e1350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1400 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1393 X0
             have i₂ := b2e1350 X0
             grind)
          | exact superpose b2e1350 b2e1393
          | exact resolve b2e1393 b2e1350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1350 b2e1393
        have b2e1845 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e129 X1 (σ X0)
             have i₂ := b2e1400 X0
             grind)
          | exact superpose b2e1400 b2e129
          | exact resolve b2e129 b2e1400
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2451 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e155 X0 x y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e155
        have b2e2454 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e2451 X0
             have j1 := b2e17 y X0
             grind)
          | (have r₁ := b2e2451 x
             have r₂ := b2e17 X0 x
             grind)
          | (have r₁ := b2e2451 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e2451 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2451
        have b2e3425 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e1845 (M.op y y) X0
             have i₂ := b2e25 y
             grind)
          | exact superpose b2e25 b2e1845
          | exact resolve b2e1845 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e3490 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) y) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e1400 (M.op X0 X0)
             have i₂ := b2e1845 X0 (σ (M.op X0 X0))
             grind)
          | exact superpose b2e1845 b2e1400
          | exact resolve b2e1400 b2e1845
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1845
        have b2e3499 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) y) = (σ (M.op (M.op X0 X0) y)) := by
          intro X0
          first
          | (have i₁ := b2e3490 X0
             have i₂ := b2e129 (M.op X0 X0) X0
             grind)
          | exact superpose b2e129 b2e3490
          | exact resolve b2e3490 b2e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129 b2e3490
        have b2e3768 : (σ y) ≠ (M.op (σ y) y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e3425 (σ y)
             grind)
          | exact superpose b2e3425 b2e22
          | exact resolve b2e22 b2e3425
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3770 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e3425 (σ x)
             grind)
          | exact superpose b2e3425 b2e19
          | exact resolve b2e19 b2e3425
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3774 : (σ (M.op y y)) = (M.op (σ y) y) := by
          first
          | (have i₁ := b2e1400 y
             have i₂ := b2e3425 (σ y)
             grind)
          | exact superpose b2e3425 b2e1400
          | exact resolve b2e1400 b2e3425
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3425
        have b2e7094 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X1) (σ X0)
             have i₂ := b2e325 X1 X0
             grind)
          | exact superpose b2e325 b2e15
          | (have j0 := b2e15 (σ X1) (σ X0)
             have j1 := b2e325 X1 X0
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e325 X0 X1
             grind)
          | exact resolve b2e15 b2e325
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e325
        have b2e7105 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e7094 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7094
        have b2e7122 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e7105 X0 X1
             have j1 := b2e986 X0 (σ X1)
             grind)
          | (have r₁ := b2e7105 X0 X1
             have r₂ := b2e986 X0 X1
             grind)
          | exact resolve b2e7105 b2e986
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e986 b2e7105
        have b2e7283 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e7122 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e7122
          | (have j0 := b2e7122 X0 X1
             grind)
          | exact resolve b2e7122 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7122
        have b2e7396 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e7283 X0 X1
             have i₂ := b2e1400 X1
             grind)
          | exact superpose b2e1400 b2e7283
          | (have j0 := b2e7283 X0 X1
             grind)
          | exact resolve b2e7283 b2e1400
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1400 b2e7283
        have b2e51973 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e7396 x y
             grind)
          | exact superpose b2e7396 b2e21
          | (have j1 := b2e7396 x y
             grind)
          | exact resolve b2e21 b2e7396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7396
        have b2e52195 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (M.op (σ y) y) := by
          first
          | (have i₁ := b2e51973
             have i₂ := b2e3774
             grind)
          | exact superpose b2e3774 b2e51973
          | exact resolve b2e51973 b2e3774
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3774 b2e51973
        have b2e836082 : (σ y) ≠ (σ (M.op y x)) ∨ (M.op (σ y) y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e52195
             have i₂ := b2e2454 x
             grind)
          | exact superpose b2e2454 b2e52195
          | (have j1 := b2e2454 x
             grind)
          | exact resolve b2e52195 b2e2454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2454 b2e52195
        have b2e836083 : (σ y) ≠ (σ y) ∨ (M.op (σ y) y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e836082
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e836082
          | exact resolve b2e836082 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e836082
        have b2e836084 : (M.op (σ y) y) = (σ (M.op y x)) ∨ x = (M.op x y) := by grind
        clear b2e836083
        have b2e836085 : (σ y) = (M.op (σ y) y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e836084
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e836084
          | exact resolve b2e836084 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e836084
        have b2e836086 : x = (M.op x y) := by
          first
          | (have r₁ := b2e836085
             have r₂ := b2e3768
             grind)
          | exact resolve b2e836085 b2e3768
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3768 b2e836085
        have b2e840133 : x = (M.op x x) := by
          first
          | (have i₁ := b2e73 x y
             have i₂ := b2e836086
             grind)
          | exact superpose b2e836086 b2e73
          | exact resolve b2e73 b2e836086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73 b2e836086
        have b2e840243 : (σ (M.op x y)) = (M.op (σ x) y) := by
          first
          | (have i₁ := b2e3499 x
             have i₂ := b2e840133
             grind)
          | exact superpose b2e840133 b2e3499
          | exact resolve b2e3499 b2e840133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3499 b2e840133
        have b2e840630 : False := by grind
        exact b2e840630
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 y y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
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
        have b3e30 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e25 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e25
          | exact resolve b3e25 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e35 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b3e15 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have r₁ := b3e15 y y
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : y = (k y y) := by grind
        clear b3e35
        have b3e43 : ∀ X0 : G, y ≠ y ∨ y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e44 X0
             have j1 := b3e15 X0 y
             grind)
          | (have r₁ := b3e44 X0
             have r₂ := b3e15 X0 y
             grind)
          | exact resolve b3e44 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e49 : ∀ X0 X1 : G, (k X0 y) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 X0
             have i₂ := b3e45 X0
             grind)
          | exact superpose b3e45 b3e16
          | (have j0 := b3e16 X1 X0
             grind)
          | exact resolve b3e16 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 X1 : G, (k X0 y) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e49 X0 X1
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e49 X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e49 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X0 X1
             have i₂ := b3e17 (σ X0) (σ X1)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X1) (σ X1)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X1 X0
             have i₂ := b3e17 X2 X0
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X1 X0
             have j1 := b3e17 X2 X0
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ y = (M.op y X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e30 X0
             have i₂ := b3e17 X1 X0
             grind)
          | exact superpose b3e17 b3e30
          | (have j1 := b3e17 X1 X0
             grind)
          | exact resolve b3e30 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e67 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b3e64 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e71 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b3e67 X0 X2 X2
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e67 X1 X0 X2
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e67 X1 X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e67 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e58 X0 X1
             have i₂ := b3e45 (σ X1)
             grind)
          | exact superpose b3e45 b3e58
          | (have j0 := b3e58 X0 X1
             grind)
          | exact resolve b3e58 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e89 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
             have i₂ := b3e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b3e12 b3e29
          | exact resolve b3e29 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e120 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e89 (M.op X0 (M.op X0 X1)) y
             have i₂ := b3e29 X0 X1
             grind)
          | exact superpose b3e29 b3e89
          | exact resolve b3e89 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e122 : (M.op (σ y) (σ y)) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e89 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e89
          | exact resolve b3e89 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e126 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e29 X0 x
             have i₂ := b3e89 X0 x
             grind)
          | exact superpose b3e89 b3e29
          | exact resolve b3e29 b3e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e134 : (k (σ y) y) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e122
             have i₂ := b3e45 (σ y)
             grind)
          | exact superpose b3e45 b3e122
          | exact resolve b3e122 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e122
        have b3e135 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e120 X0 x
             have i₂ := b3e89 X0 x
             grind)
          | exact superpose b3e89 b3e120
          | exact resolve b3e120 b3e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120
        have b3e154 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op X0 y) y X1
             have i₂ := b3e126 X0
             grind)
          | exact superpose b3e126 b3e12
          | exact resolve b3e12 b3e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e126
        have b3e155 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e154 X0 X1
             have i₂ := b3e135 X0
             grind)
          | exact superpose b3e135 b3e154
          | exact resolve b3e154 b3e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135 b3e154
        have b3e301 : (σ y) = (k (M.op (σ y) (σ y)) y) := by
          first
          | (have i₁ := b3e45 (M.op (σ y) (σ y))
             have i₂ := b3e26 (σ y)
             grind)
          | exact superpose b3e26 b3e45
          | exact resolve b3e45 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e312 : (σ y) = (k (k (σ y) y) y) := by
          first
          | (have i₁ := b3e301
             have i₂ := b3e45 (σ y)
             grind)
          | exact superpose b3e45 b3e301
          | exact resolve b3e301 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e301
        have b3e337 : (σ y) = (k (M.op (σ y) y) y) := by
          first
          | (have i₁ := b3e312
             have i₂ := b3e134
             grind)
          | exact superpose b3e134 b3e312
          | exact resolve b3e312 b3e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e312
        have b3e602 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e71 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e608 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e602 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e602 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e602 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e602
        have b3e1112 : ∀ X0 : G, (σ y) = (M.op (σ (k y y)) (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) y) := by
          intro X0
          first
          | (have i₁ := b3e26 X0
             have i₂ := b3e72 y y
             grind)
          | exact superpose b3e72 b3e26
          | (have j1 := b3e72 y y
             grind)
          | exact resolve b3e26 b3e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e72
        have b3e1180 : (σ y) = (M.op (σ (k y y)) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b3e1112 x
             have i₂ := b3e155 (σ (k y y)) x
             grind)
          | exact superpose b3e155 b3e1112
          | exact resolve b3e1112 b3e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e155 b3e1112
        have b3e1202 : (σ y) = (M.op (σ y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b3e1180
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e1180
          | exact resolve b3e1180 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1180
        have b3e1210 : (σ y) = (k (σ y) y) ∨ (σ y) = (M.op (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b3e1202
             have i₂ := b3e45 (σ y)
             grind)
          | exact superpose b3e45 b3e1202
          | exact resolve b3e1202 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1202
        have b3e1211 : (σ y) = (k (σ y) y) ∨ (σ y) = (M.op (σ y) y) := by grind
        clear b3e1210
        have b3e1215 : (σ y) = (M.op (σ y) y) ∨ (σ y) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e1211
             have i₂ := b3e134
             grind)
          | exact superpose b3e134 b3e1211
          | exact resolve b3e1211 b3e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134 b3e1211
        have b3e1216 : (σ y) = (M.op (σ y) y) := by grind
        clear b3e1215
        have b3e1223 : (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b3e337
             have i₂ := b3e1216
             grind)
          | exact superpose b3e1216 b3e337
          | exact resolve b3e337 b3e1216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e337 b3e1216
        have b3e1846 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e53 (σ y) X0
             have i₂ := b3e1223
             grind)
          | exact superpose b3e1223 b3e53
          | (have j0 := b3e53 (σ y) X0
             grind)
          | (have r₁ := b3e53 (σ y) x
             have r₂ := b3e1223
             grind)
          | exact resolve b3e53 b3e1223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e1851 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e1846 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1846
        have b3e1905 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e1851 (σ X0)
             grind)
          | exact superpose b3e1851 b3e18
          | exact resolve b3e18 b3e1851
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1851
        have b3e1911 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e1905 X0
             have i₂ := b3e45 (σ X0)
             grind)
          | exact superpose b3e45 b3e1905
          | exact resolve b3e1905 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1905
        have b3e2360 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e608 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e608
          | (have j0 := b3e608 (σ y) (σ x)
             grind)
          | exact resolve b3e608 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e608
        have b3e2411 : (σ y) ≠ (k (σ y) y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e2360
             have i₂ := b3e45 (σ y)
             grind)
          | exact superpose b3e45 b3e2360
          | exact resolve b3e2360 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2360
        have b3e2437 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b3e2411
             have r₂ := b3e1223
             grind)
          | exact resolve b3e2411 b3e1223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1223 b3e2411
        have b3e2450 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e2437
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e2437
          | exact resolve b3e2437 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2437
        have b3e2460 : (k (σ y) y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e2450
             have i₂ := b3e45 (σ y)
             grind)
          | exact superpose b3e45 b3e2450
          | exact resolve b3e2450 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e2450
        have b3e2468 : (σ (k y x)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e2460
             have i₂ := b3e1911 y
             grind)
          | exact superpose b3e1911 b3e2460
          | exact resolve b3e2460 b3e1911
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1911 b3e2460
        have b3e2473 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e2468
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e2468
          | exact resolve b3e2468 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e2468
        have b3e2958 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y x)
             have i₂ := b3e2473
             grind)
          | exact superpose b3e2473 b3e13
          | exact resolve b3e13 b3e2473
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2473
        have b3e2985 : y = (k y x) := by
          first
          | (have i₁ := b3e2958
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e2958
          | exact resolve b3e2958 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2958
        have b3e4204 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e2985
             have i₂ := b3e65 x y
             grind)
          | exact superpose b3e65 b3e2985
          | (have j1 := b3e65 x y
             grind)
          | exact resolve b3e2985 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e2985
        have b3e4208 : y = (M.op y x) ∨ x = (M.op x y) := by grind
        clear b3e4204
        have b3e4224 : x = (M.op x y) := by
          first
          | (have r₁ := b3e4208
             have r₂ := b3e20
             grind)
          | exact resolve b3e4208 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4208
        have b3e4243 : x = (M.op x x) := by
          first
          | (have i₁ := b3e89 x y
             have i₂ := b3e4224
             grind)
          | exact superpose b3e4224 b3e89
          | exact resolve b3e89 b3e4224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89 b3e4224
        have b3e4279 : y = (M.op y x) := by
          first
          | (have i₁ := b3e30 x
             have i₂ := b3e4243
             grind)
          | exact superpose b3e4243 b3e30
          | exact resolve b3e30 b3e4243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e4243
        have b3e4314 : False := by grind
        exact b3e4314
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
          have b4e31 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
               have i₂ := b4e13 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
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
          have b4e36 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (σ y)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e32 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e38 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e31 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e31
            | exact resolve b4e31 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e52 : ∀ X0 : G, y ≠ y ∨ y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 X0 y
               grind)
            | (have r₁ := b4e17 X0 y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e53 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 X0 (σ y)
               grind)
            | (have r₁ := b4e17 X0 (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b4e53 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e55 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b4e52 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b4e54 X0
               have j1 := b4e16 X0 (σ y)
               grind)
            | (have r₁ := b4e54 X0
               have r₂ := b4e16 X0 (σ y)
               grind)
            | exact resolve b4e54 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b4e55 X0
               have j1 := b4e16 X0 y
               grind)
            | (have r₁ := b4e55 X0
               have r₂ := b4e16 X0 y
               grind)
            | exact resolve b4e55 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e68 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X0 X1
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X2 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e99 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e57 X0
               have i₂ := b4e56 X0
               grind)
            | exact superpose b4e56 b4e57
            | exact resolve b4e57 b4e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e105 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 y
               have i₂ := b4e56 (σ X0)
               grind)
            | exact superpose b4e56 b4e19
            | exact resolve b4e19 b4e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e108 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e105 X0
               have i₂ := b4e57 (σ X0)
               grind)
            | exact superpose b4e57 b4e105
            | exact resolve b4e105 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e134 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
               have i₂ := b4e13 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e204 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
               have i₂ := b4e13 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b4e13 b4e36
            | exact resolve b4e36 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e212 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e204 X0 x
               have i₂ := b4e134 X0 x
               grind)
            | exact superpose b4e134 b4e204
            | exact resolve b4e204 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204
          have b4e247 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e34 (M.op X0 (M.op X0 X1)) (M.op x x) X3
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e264 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 (k X0 y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 X1 X2 X0
               have i₂ := b4e57 X0
               grind)
            | exact superpose b4e57 b4e34
            | exact resolve b4e34 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e305 : ∀ X0 X1 : G, (M.op X1 (k X0 y)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e264 X0 X1 x
               have i₂ := b4e134 X1 x
               grind)
            | exact superpose b4e134 b4e264
            | exact resolve b4e264 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e264
          have b4e317 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e247 X0 X1 x
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e247
            | exact resolve b4e247 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e247
          have b4e322 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e317 X0 x
               have i₂ := b4e134 X0 x
               grind)
            | exact superpose b4e134 b4e317
            | exact resolve b4e317 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134 b4e317
          have b4e331 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 y) X0 X1
               have i₂ := b4e322 X0
               grind)
            | exact superpose b4e322 b4e13
            | exact resolve b4e13 b4e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e332 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e331 X0 X1
               have i₂ := b4e322 X0
               grind)
            | exact superpose b4e322 b4e331
            | exact resolve b4e331 b4e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e331
          have b4e481 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e212 (σ x)
               grind)
            | exact superpose b4e212 b4e20
            | exact resolve b4e20 b4e212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e212
          have b4e719 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (M.op (σ X1) (σ X1)) (M.op X2 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e68 (σ X1) X2 (σ X0)
               grind)
            | exact superpose b4e68 b4e19
            | (have j1 := b4e68 (σ X1) X2 (σ X0)
               grind)
            | exact resolve b4e19 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e722 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) (σ X1)) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e719 X0 X1 x
               have i₂ := b4e332 (M.op (σ X1) (σ X1)) x
               grind)
            | exact superpose b4e332 b4e719
            | (have j0 := b4e719 X0 X1 x
               grind)
            | exact resolve b4e719 b4e332
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e332 b4e719
          have b4e754 : ∀ X0 X1 : G, (σ X1) = (M.op (k (σ X1) y) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e722 X0 X1
               have i₂ := b4e57 (σ X1)
               grind)
            | exact superpose b4e57 b4e722
            | (have j0 := b4e722 X0 X1
               grind)
            | exact resolve b4e722 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e722
          have b4e767 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X1 y)) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e754 X0 X1
               have i₂ := b4e108 X1
               grind)
            | exact superpose b4e108 b4e754
            | (have j0 := b4e754 X0 X1
               grind)
            | exact resolve b4e754 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e754
          have b4e1592 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (k X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b4e37 (k X0 y)
               have i₂ := b4e305 X0 (k X0 y)
               grind)
            | exact superpose b4e305 b4e37
            | exact resolve b4e37 b4e305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e1593 : ∀ X0 : G, y = (M.op y (M.op (k X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b4e38 (k X0 y)
               have i₂ := b4e305 X0 (k X0 y)
               grind)
            | exact superpose b4e305 b4e38
            | exact resolve b4e38 b4e305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e305
          have b4e31721 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) y) ∨ (σ X0) = (M.op (σ (k X0 y)) y) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 (σ X0) (σ X1)
               have i₂ := b4e767 X1 X0
               grind)
            | exact superpose b4e767 b4e35
            | (have j1 := b4e767 X1 X0
               grind)
            | exact resolve b4e35 b4e767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e767
          have b4e31743 : ∀ X0 X1 : G, (σ X0) = (M.op (k (σ X0) y) y) ∨ (σ X0) = (M.op (σ (k X0 y)) y) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31721 X0 X1
               have i₂ := b4e57 (σ X0)
               grind)
            | exact superpose b4e57 b4e31721
            | (have j0 := b4e31721 X0 X1
               grind)
            | exact resolve b4e31721 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57 b4e31721
          have b4e31951 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 y)) y) ∨ (σ X0) = (M.op (σ (k X0 y)) y) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31743 X0 X1
               have i₂ := b4e108 X0
               grind)
            | exact superpose b4e108 b4e31743
            | (have j0 := b4e31743 X0 X1
               grind)
            | exact resolve b4e31743 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108 b4e31743
          have b4e31952 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 y)) y) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e31951 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31951
          have b4e102281 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ (k (τ X0) y)) y) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e31952 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e31952
            | exact resolve b4e31952 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31952
          have b4e102729 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ (k (τ X0) y)) y) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e102281 X0 X1
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e102281
            | (have j0 := b4e102281 X0 X1
               grind)
            | exact resolve b4e102281 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e102281
          have b4e102882 : ∀ X0 X1 : G, (M.op (k X0 (σ y)) y) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e102729 X0 X1
               have i₂ := b4e25 X0 y
               grind)
            | exact superpose b4e25 b4e102729
            | (have j0 := b4e102729 X0 X1
               grind)
            | exact resolve b4e102729 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e102729
          have b4e102940 : ∀ X0 X1 : G, (M.op (k X0 y) y) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e102882 X0 X1
               have i₂ := b4e99 X0
               grind)
            | exact superpose b4e99 b4e102882
            | (have j0 := b4e102882 X0 X1
               grind)
            | exact resolve b4e102882 b4e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99 b4e102882
          have b4e725638 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op (k X1 y) y) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e102940 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e102940
            | (have j0 := b4e102940 X1 X1
               grind)
            | exact resolve b4e102940 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102940
          have b4e727378 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1592 X0
               have i₂ := b4e725638 X1 X0
               grind)
            | exact superpose b4e725638 b4e1592
            | (have j1 := b4e725638 X1 X0
               grind)
            | exact resolve b4e1592 b4e725638
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1592
          have b4e727379 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ y = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1593 X0
               have i₂ := b4e725638 X1 X0
               grind)
            | exact superpose b4e725638 b4e1593
            | (have j1 := b4e725638 X1 X0
               grind)
            | exact resolve b4e1593 b4e725638
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1593 b4e725638
          have b4e743626 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e727378 (σ x) X0
               grind)
            | exact superpose b4e727378 b4e23
            | (have j1 := b4e727378 (σ x) X0
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e727378 (σ x) x
               grind)
            | exact resolve b4e23 b4e727378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e727378
          have b4e744412 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e743626 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e743626
          have b4e744773 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e30 X0 x
               have i₂ := b4e744412 X0
               grind)
            | exact superpose b4e744412 b4e30
            | exact resolve b4e30 b4e744412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e744412
          have b4e744939 : (τ (σ x)) = (k (τ (M.op (σ x) y)) x) := by
            first
            | (have i₁ := b4e744773 (M.op (σ x) y)
               have i₂ := b4e322 (σ x)
               grind)
            | exact superpose b4e322 b4e744773
            | exact resolve b4e744773 b4e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e322 b4e744773
          have b4e745000 : x = (k (τ (M.op (σ x) y)) x) := by
            first
            | (have i₁ := b4e744939
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e744939
            | exact resolve b4e744939 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e744939
          have b4e745332 : x = (M.op (τ (M.op (σ x) y)) x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b4e727379 x (τ (M.op (σ x) y))
               have i₂ := b4e745000
               grind)
            | exact superpose b4e745000 b4e727379
            | (have j0 := b4e727379 x x
               grind)
            | exact resolve b4e727379 b4e745000
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e727379 b4e745000
          have b4e745337 : x = (M.op (τ (M.op (σ x) y)) x) := by
            first
            | (have r₁ := b4e745332
               have r₂ := b4e21
               grind)
            | exact resolve b4e745332 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e745332
          have b4e745383 : (τ (M.op (σ x) y)) = (M.op (M.op (τ (M.op (σ x) y)) x) y) := by
            first
            | (have i₁ := b4e35 (τ (M.op (σ x) y)) x
               have i₂ := b4e745337
               grind)
            | exact superpose b4e745337 b4e35
            | exact resolve b4e35 b4e745337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e745394 : (M.op x y) = (τ (M.op (σ x) y)) := by
            first
            | (have i₁ := b4e745383
               have i₂ := b4e745337
               grind)
            | exact superpose b4e745337 b4e745383
            | exact resolve b4e745383 b4e745337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e745337 b4e745383
          have b4e747665 : (σ (M.op x y)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e15 (M.op (σ x) y)
               have i₂ := b4e745394
               grind)
            | exact superpose b4e745394 b4e15
            | exact resolve b4e15 b4e745394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e745394
          have b4e747697 : False := by grind
          exact b4e747697
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e40 : y ≠ y ∨ y = (k y y) := by
            first
            | (have i₁ := b5e16 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have r₁ := b5e16 y y
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : y = (k y y) := by grind
          clear b5e40
          have b5e45 : ∀ X0 : G, y ≠ y ∨ y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b5e45 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b5e46 X0
               have j1 := b5e16 X0 y
               grind)
            | (have r₁ := b5e46 X0
               have r₂ := b5e16 X0 y
               grind)
            | exact resolve b5e46 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e54 : (σ y) ≠ (k (σ y) y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e47 (σ y)
               grind)
            | exact superpose b5e47 b5e24
            | exact resolve b5e24 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e62 X0 X1
               have i₂ := b5e47 (σ X1)
               grind)
            | exact superpose b5e47 b5e62
            | (have j0 := b5e62 X0 X1
               grind)
            | exact resolve b5e62 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e1005 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) y) := by
            intro X0
            first
            | (have j0 := b5e78 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e1009 : ∀ X0 : G, (σ X0) = (k (σ X0) y) ∨ (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b5e1005 X0
               have i₂ := b5e47 (σ X0)
               grind)
            | exact superpose b5e47 b5e1005
            | (have j0 := b5e1005 X0
               grind)
            | exact resolve b5e1005 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e1005
          have b5e1010 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) y) := by
            intro X0
            first
            | (have j0 := b5e1009 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1009
          have b5e2707 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) y) := by
            first
            | (have i₁ := b5e1010 y
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e1010
            | (have j0 := b5e1010 y
               grind)
            | exact resolve b5e1010 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e1010
          have b5e2710 : (σ y) = (k (σ y) y) := by grind
          clear b5e2707
          have b5e2715 : False := by grind
          exact b5e2715
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b6e25 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e12 (M.op X0 (M.op X0 X1)) (M.op x x) X3
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
             have i₂ := b6e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e23 X0 X1
             grind)
          | exact superpose b6e23 b6e13
          | exact resolve b6e13 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e32 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e34 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e32
        have b6e35 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e34
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e34
          | exact resolve b6e34 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e44 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e15
          | exact resolve b6e15 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e49 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e44
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e44
          | exact resolve b6e44 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X0 X1
             have i₂ := b6e17 (σ X0) (σ X1)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X1) (σ X1)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e17 X2 X0
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X1 X0
             have j1 := b6e17 X2 X0
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b6e57 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e62 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b6e60 X0 X2 X2
             have j1 := b6e15 X1 X0
             grind)
          | (have r₁ := b6e60 X1 X0 X2
             have r₂ := b6e15 X0 X1
             grind)
          | (have r₁ := b6e60 X1 X1 X0
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e60 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e31 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e31
          | exact resolve b6e31 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e74 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e27 (M.op X0 (M.op X0 X1)) (M.op x x) X3
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e27
          | exact resolve b6e27 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e79 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e27 X0 x X3
             have i₂ := b6e27 X0 x X1
             grind)
          | (have i₁ := b6e27 x x x
             have i₂ := b6e27 x X1 x
             grind)
          | exact superpose b6e27 b6e27
          | exact resolve b6e27 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e94 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e74 X0 X1 x
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e74
          | exact resolve b6e74 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e103 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e94 X0 x
             have i₂ := b6e27 X0 x X1
             grind)
          | (have i₁ := b6e94 x x
             have i₂ := b6e27 x X1 x
             grind)
          | exact superpose b6e27 b6e94
          | exact resolve b6e94 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e138 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e103 X0 (M.op (σ y) (σ y))
             have i₂ := b6e25 (σ y)
             grind)
          | exact superpose b6e25 b6e103
          | exact resolve b6e103 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e103
        have b6e219 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op X0 (σ y)) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e27 (M.op X0 (σ y)) X0 X1
             have i₂ := b6e138 X0
             grind)
          | exact superpose b6e138 b6e27
          | exact resolve b6e27 b6e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e221 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X0 (σ y)) X0 X1
             have i₂ := b6e138 X0
             grind)
          | exact superpose b6e138 b6e12
          | exact resolve b6e12 b6e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e223 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e221 X0 X1
             have i₂ := b6e138 X0
             grind)
          | exact superpose b6e138 b6e221
          | exact resolve b6e221 b6e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e221
        have b6e224 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e219 X0 X1
             have i₂ := b6e138 X0
             grind)
          | exact superpose b6e138 b6e219
          | exact resolve b6e219 b6e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e138 b6e219
        have b6e227 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e224 X0 x
             have i₂ := b6e223 (M.op X0 (σ y)) x
             grind)
          | exact superpose b6e223 b6e224
          | exact resolve b6e224 b6e223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e224
        have b6e309 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e62 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e313 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e309 X0 X1
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e309 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e309 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e309
        have b6e739 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e52 x x
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e52
          | exact resolve b6e52 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e52
        have b6e820 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
        clear b6e739
        have b6e850 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b6e820
             have r₂ := b6e49
             grind)
          | exact resolve b6e820 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e820
        have b6e867 : (k x x) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e850
             grind)
          | exact superpose b6e850 b6e13
          | exact resolve b6e13 b6e850
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e850
        have b6e882 : (k x y) = (k x x) := by
          first
          | (have i₁ := b6e867
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e867
          | exact resolve b6e867 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e867
        have b6e2821 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e313 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e313
        have b6e2876 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e2821 (σ X0)
             grind)
          | exact superpose b6e2821 b6e18
          | exact resolve b6e18 b6e2821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2878 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e63 X0 X0
             have i₂ := b6e2821 (τ X0)
             grind)
          | exact superpose b6e2821 b6e63
          | exact resolve b6e63 b6e2821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e2880 : (k x y) = (M.op x x) := by
          first
          | (have i₁ := b6e882
             have i₂ := b6e2821 x
             grind)
          | exact superpose b6e2821 b6e882
          | exact resolve b6e882 b6e2821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e882
        have b6e2883 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e2878 X0
             have i₂ := b6e2821 X0
             grind)
          | exact superpose b6e2821 b6e2878
          | exact resolve b6e2878 b6e2821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2878
        have b6e2885 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e2876 X0
             have i₂ := b6e2821 X0
             grind)
          | exact superpose b6e2821 b6e2876
          | exact resolve b6e2876 b6e2821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2821 b6e2876
        have b6e2968 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e2880
             grind)
          | exact superpose b6e2880 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e2880
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2880
        have b6e2969 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e2968
             have r₂ := b6e21
             grind)
          | exact resolve b6e2968 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2968
        have b6e2981 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e2969
             have r₂ := b6e20
             grind)
          | exact resolve b6e2969 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2969
        have b6e3066 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b6e223 X0 x
             have i₂ := b6e2981
             grind)
          | exact superpose b6e2981 b6e223
          | exact resolve b6e223 b6e2981
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3369 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (τ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e223 X1 (τ X0)
             have i₂ := b6e2883 X0
             grind)
          | exact superpose b6e2883 b6e223
          | exact resolve b6e223 b6e2883
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2883
        have b6e4204 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (τ (σ y))) := by
          intro X0
          first
          | (have i₁ := b6e3369 (M.op (σ y) (σ y)) X0
             have i₂ := b6e25 (σ y)
             grind)
          | exact superpose b6e25 b6e3369
          | exact resolve b6e3369 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25 b6e3369
        have b6e4299 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e4204 X0
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e4204
          | exact resolve b6e4204 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4204
        have b6e4393 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) (M.op (σ y) y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e26 X0 X1 (σ y)
             have i₂ := b6e4299 (σ y)
             grind)
          | exact superpose b6e4299 b6e26
          | exact resolve b6e26 b6e4299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e4406 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) y)) := by
          intro X0
          first
          | (have i₁ := b6e223 X0 (σ y)
             have i₂ := b6e4299 (σ y)
             grind)
          | exact superpose b6e4299 b6e223
          | exact resolve b6e223 b6e4299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e223
        have b6e4432 : ∀ X0 : G, (M.op (M.op X0 (σ y)) y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e227 X0
             have i₂ := b6e4299 (M.op X0 (σ y))
             grind)
          | exact superpose b6e4299 b6e227
          | exact resolve b6e227 b6e4299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e227
        have b6e4444 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e4299 (σ x)
             grind)
          | exact superpose b6e4299 b6e19
          | exact resolve b6e19 b6e4299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4458 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e4432 X0
             have i₂ := b6e4299 X0
             grind)
          | exact superpose b6e4299 b6e4432
          | exact resolve b6e4432 b6e4299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4432
        have b6e4469 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (σ y) y)) := by
          intro X0
          first
          | (have i₁ := b6e4406 X0
             have i₂ := b6e4299 X0
             grind)
          | exact superpose b6e4299 b6e4406
          | exact resolve b6e4406 b6e4299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4406
        have b6e4479 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (σ y) y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e4393 X0 X1
             have i₂ := b6e94 X0 X1
             grind)
          | exact superpose b6e94 b6e4393
          | exact resolve b6e4393 b6e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e94 b6e4393
        have b6e4517 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b6e4479 X0 X1
             have i₂ := b6e4469 X0
             grind)
          | exact superpose b6e4469 b6e4479
          | exact resolve b6e4479 b6e4469
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4469 b6e4479
        have b6e5966 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e79 X0 X1 X0
             have i₂ := b6e4517 X0 X0
             grind)
          | exact superpose b6e4517 b6e79
          | exact resolve b6e79 b6e4517
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79 b6e4517
        have b6e6608 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) (σ y))) := by
          intro X0
          first
          | (have i₁ := b6e5966 X0 (M.op x y)
             have i₂ := b6e3066 (M.op x y)
             grind)
          | exact superpose b6e3066 b6e5966
          | exact resolve b6e5966 b6e3066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3066
        have b6e6619 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e5966 X1 (σ X0)
             have i₂ := b6e2885 X0
             grind)
          | exact superpose b6e2885 b6e5966
          | exact resolve b6e5966 b6e2885
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e6624 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b6e5966 X0 x
             have i₂ := b6e2981
             grind)
          | exact superpose b6e2981 b6e5966
          | exact resolve b6e5966 b6e2981
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2981 b6e5966
        have b6e6810 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) y)) := by
          intro X0
          first
          | (have i₁ := b6e6608 X0
             have i₂ := b6e4299 (M.op x y)
             grind)
          | exact superpose b6e4299 b6e6608
          | exact resolve b6e6608 b6e4299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4299 b6e6608
        have b6e6866 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e6810 X0
             have i₂ := b6e4458 x
             grind)
          | exact superpose b6e4458 b6e6810
          | exact resolve b6e6810 b6e4458
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6810
        have b6e10491 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op (M.op x y) y))) := by
          intro X0
          first
          | (have i₁ := b6e6619 (M.op x y) X0
             have i₂ := b6e6624 (M.op x y)
             grind)
          | exact superpose b6e6624 b6e6619
          | exact resolve b6e6619 b6e6624
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6619 b6e6624
        have b6e10681 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e10491 X0
             have i₂ := b6e4458 x
             grind)
          | exact superpose b6e4458 b6e10491
          | exact resolve b6e10491 b6e4458
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4458 b6e10491
        have b6e10975 : (σ (M.op x x)) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e2885 x
             have i₂ := b6e10681 (σ x)
             grind)
          | exact superpose b6e10681 b6e2885
          | exact resolve b6e2885 b6e10681
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2885 b6e10681
        have b6e10985 : (σ (M.op x y)) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e10975
             have i₂ := b6e6866 x
             grind)
          | exact superpose b6e6866 b6e10975
          | exact resolve b6e10975 b6e6866
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6866 b6e10975
        have b6e11040 : False := by grind
        exact b6e11040
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have r₁ := b7e16 (σ y) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b7e40
          have b7e45 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e44
            | exact resolve b7e44 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e14
            | exact resolve b7e14 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : y = (k y y) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e48
            | exact resolve b7e48 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e59 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e18 y y
               grind)
            | exact superpose b7e18 b7e49
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e49 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e69 : y = (M.op y y) := by grind
          clear b7e59
          have b7e73 : False := by grind
          exact b7e73
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e841 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e63 x y
               grind)
            | exact superpose b8e63 b8e20
            | (have j1 := b8e63 y y
               grind)
            | exact resolve b8e20 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e973 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e841
               have r₂ := b8e24
               grind)
            | exact resolve b8e841 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e841
          have b8e1015 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e973
               have r₂ := b8e23
               grind)
            | exact resolve b8e973 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e973
          have b8e1029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1015
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1015
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e1015 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1015
          have b8e1030 : y = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e1029
          have b8e1033 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1030
               have r₂ := b8e22
               grind)
            | exact resolve b8e1030 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1030
          have b8e1036 : False := by grind
          exact b8e1036

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : (M.op y x) = (M.op y y) := by grind
        have b0e21 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        have b0e22 : (M.op x y) = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e39 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X0)) := by
          intro X0
          first
          | (have i₁ := b0e12 X0 (σ x) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e12
          | exact resolve b0e12 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e39 X0
             have i₂ := b0e12 X0 (σ y) (σ y)
             grind)
          | exact superpose b0e12 b0e39
          | exact resolve b0e39 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e44 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b0e15 x y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e15
          | (have j0 := b0e15 y y
             grind)
          | (have r₁ := b0e15 x y
             have r₂ := b0e20
             grind)
          | exact resolve b0e15 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e48 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e15 (σ x) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e15
          | (have j0 := b0e15 (σ y) (σ y)
             grind)
          | (have r₁ := b0e15 (σ x) (σ y)
             have r₂ := b0e21
             grind)
          | exact resolve b0e15 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e54 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b0e48
        have b0e56 : (M.op x x) = (k x y) := by grind
        clear b0e44
        have b0e58 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b0e54
             have i₂ := b0e40 (σ x)
             grind)
          | exact superpose b0e40 b0e54
          | exact resolve b0e54 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40 b0e54
        have b0e62 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b0e56
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e56
          | exact resolve b0e56 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e56
        have b0e63 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b0e58
             have i₂ := b0e18 x y
             grind)
          | exact superpose b0e18 b0e58
          | exact resolve b0e58 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e58
        have b0e64 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e63
             have i₂ := b0e62
             grind)
          | exact superpose b0e62 b0e63
          | exact resolve b0e63 b0e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e62 b0e63
        have b0e65 : False := by grind
        exact b0e65
      · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b1e21 : (M.op y x) = (M.op y y) := by grind
          have b1e23 : (M.op x y) ≠ (M.op x x) := by grind
          have b1e24 : (M.op x y) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e23
            | exact resolve b1e23 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e29 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) X0)) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 x y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e34 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b1e29 X0
               have i₂ := b1e13 X0 y y
               grind)
            | exact superpose b1e13 b1e29
            | exact resolve b1e29 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e29
          have b1e37 : (M.op x y) ≠ (M.op y y) := by
            first
            | (have i₁ := b1e25
               have i₂ := b1e34 x
               grind)
            | exact superpose b1e34 b1e25
            | exact resolve b1e25 b1e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e25 b1e34
          have b1e38 : False := by grind
          exact b1e38
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b2e21 : (M.op y x) = (M.op y y) := by grind
          have b2e23 : (M.op x y) ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e27 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) X0)) := by
            intro X0
            first
            | (have i₁ := b2e13 X0 x y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e31 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e27 X0
               have i₂ := b2e13 X0 y y
               grind)
            | exact superpose b2e13 b2e27
            | exact resolve b2e27 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e27
          have b2e32 : (M.op x y) ≠ (M.op x y) := by
            first
            | (have i₁ := b2e23
               have i₂ := b2e31 x
               grind)
            | exact superpose b2e31 b2e23
            | (have r₁ := b2e23
               have r₂ := b2e31 x
               grind)
            | exact resolve b2e23 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31
          have b2e35 : False := by grind
          exact b2e35
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : (M.op y x) = (M.op y y) := by grind
          have b3e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b3e23 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : (M.op x y) = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e34 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X0)) := by
            intro X0
            first
            | (have i₁ := b3e13 X0 y x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e38 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b3e34 X0
               have i₂ := b3e13 X0 x x
               grind)
            | exact superpose b3e13 b3e34
            | exact resolve b3e34 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e34
          have b3e65 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b3e16 X0 y
               have i₂ := b3e38 y
               grind)
            | exact superpose b3e38 b3e16
            | (have j0 := b3e16 X0 y
               grind)
            | (have r₁ := b3e16 y x
               have r₂ := b3e38 x
               grind)
            | (have r₁ := b3e16 x y
               have r₂ := b3e38 y
               grind)
            | exact resolve b3e16 b3e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e38
          have b3e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b3e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b3e19 X0 X0
               have i₂ := b3e66 (σ X0)
               grind)
            | exact superpose b3e66 b3e19
            | exact resolve b3e19 b3e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b3e74 X0
               have i₂ := b3e66 X0
               grind)
            | exact superpose b3e66 b3e74
            | exact resolve b3e74 b3e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e66 b3e74
          have b3e88 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e17 (σ x) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 (σ x) (σ x)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e92 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b3e88
          have b3e95 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e92
               have r₂ := b3e25
               grind)
            | exact resolve b3e92 b3e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e92
          have b3e99 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b3e95
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e95
            | exact resolve b3e95 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e95
          have b3e100 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b3e99
               have i₂ := b3e81 y
               grind)
            | exact superpose b3e81 b3e99
            | exact resolve b3e99 b3e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e99
          have b3e101 : (σ (k x y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b3e100
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e100
            | exact resolve b3e100 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e100
          have b3e282 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b3e25
               have i₂ := b3e81 y
               grind)
            | exact superpose b3e81 b3e25
            | exact resolve b3e25 b3e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e25
          have b3e296 : (M.op (σ x) (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b3e282
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e282
            | exact resolve b3e282 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e282
          have b3e298 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b3e296
               have i₂ := b3e81 x
               grind)
            | exact superpose b3e81 b3e296
            | exact resolve b3e296 b3e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e81 b3e296
          have b3e1659 : (M.op x x) = (k x y) := by
            first
            | (have j0 := b3e65 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e65
          have b3e2090 : (σ (M.op x x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b3e101
               have i₂ := b3e1659
               grind)
            | exact superpose b3e1659 b3e101
            | exact resolve b3e101 b3e1659
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e101 b3e1659
          have b3e2100 : False := by grind
          exact b3e2100
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b4e22 : (M.op y x) = (M.op y y) := by grind
            have b4e25 : (M.op x y) ≠ (M.op x x) := by grind
            have b4e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : (M.op y y) ≠ (M.op x x) := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e25
              | exact resolve b4e25 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e31 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) X0)) := by
              intro X0
              first
              | (have i₁ := b4e14 X0 x y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e14
              | exact resolve b4e14 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e36 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b4e31 X0
                 have i₂ := b4e14 X0 y y
                 grind)
              | exact superpose b4e14 b4e31
              | exact resolve b4e31 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e31
            have b4e39 : (M.op x y) ≠ (M.op y y) := by
              first
              | (have i₁ := b4e27
                 have i₂ := b4e36 x
                 grind)
              | exact superpose b4e36 b4e27
              | exact resolve b4e27 b4e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e27 b4e36
            have b4e40 : False := by grind
            exact b4e40
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b5e22 : (M.op y x) = (M.op y y) := by grind
            have b5e25 : (M.op x y) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e29 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) X0)) := by
              intro X0
              first
              | (have i₁ := b5e14 X0 x y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e33 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b5e29 X0
                 have i₂ := b5e14 X0 y y
                 grind)
              | exact superpose b5e14 b5e29
              | exact resolve b5e29 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29
            have b5e34 : (M.op x y) ≠ (M.op x y) := by
              first
              | (have i₁ := b5e25
                 have i₂ := b5e33 x
                 grind)
              | exact superpose b5e33 b5e25
              | (have r₁ := b5e25
                 have r₂ := b5e33 x
                 grind)
              | exact resolve b5e25 b5e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e33
            have b5e37 : False := by grind
            exact b5e37
      · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b6e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : (M.op x y) = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e33 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X0)) := by
            intro X0
            first
            | (have i₁ := b6e13 X0 y x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e37 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b6e33 X0
               have i₂ := b6e13 X0 x x
               grind)
            | exact superpose b6e13 b6e33
            | exact resolve b6e33 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33
          have b6e63 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b6e16 X0 y
               have i₂ := b6e37 y
               grind)
            | exact superpose b6e37 b6e16
            | (have j0 := b6e16 X0 y
               grind)
            | (have r₁ := b6e16 y x
               have r₂ := b6e37 x
               grind)
            | (have r₁ := b6e16 x y
               have r₂ := b6e37 y
               grind)
            | exact resolve b6e16 b6e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e37
          have b6e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b6e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b6e19 X0 X0
               have i₂ := b6e64 (σ X0)
               grind)
            | exact superpose b6e64 b6e19
            | exact resolve b6e19 b6e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b6e72 X0
               have i₂ := b6e64 X0
               grind)
            | exact superpose b6e64 b6e72
            | exact resolve b6e72 b6e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e64 b6e72
          have b6e110 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e22
               have i₂ := b6e18 X0 (σ y)
               grind)
            | (have i₁ := b6e22
               have i₂ := b6e18 (σ y) (σ y)
               grind)
            | exact superpose b6e18 b6e22
            | (have j1 := b6e18 X0 (σ y)
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e22 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e1165 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b6e110 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e110
          have b6e1166 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e1165
               have r₂ := b6e23
               grind)
            | exact resolve b6e1165 b6e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1165
          have b6e1173 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e1166
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e1166
            | exact resolve b6e1166 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1166
          have b6e1178 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e1173
               grind)
            | exact superpose b6e1173 b6e23
            | exact resolve b6e23 b6e1173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1173
          have b6e1190 : (σ (M.op x x)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b6e1178
               have i₂ := b6e79 x
               grind)
            | exact superpose b6e79 b6e1178
            | exact resolve b6e1178 b6e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e79 b6e1178
          have b6e4317 : (M.op x x) = (k x y) := by
            first
            | (have j0 := b6e63 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e63
          have b6e5181 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b6e1190
               have i₂ := b6e4317
               grind)
            | exact superpose b6e4317 b6e1190
            | exact resolve b6e1190 b6e4317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1190 b6e4317
          have b6e5195 : False := by grind
          exact b6e5195
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b7e22 : (M.op y x) = (M.op y y) := by grind
            have b7e25 : (M.op x y) ≠ (M.op x x) := by grind
            have b7e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : (M.op y y) ≠ (M.op x x) := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e25
              | exact resolve b7e25 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e31 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) X0)) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e36 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b7e31 X0
                 have i₂ := b7e14 X0 y y
                 grind)
              | exact superpose b7e14 b7e31
              | exact resolve b7e31 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e31
            have b7e39 : (M.op x y) ≠ (M.op y y) := by
              first
              | (have i₁ := b7e27
                 have i₂ := b7e36 x
                 grind)
              | exact superpose b7e36 b7e27
              | exact resolve b7e27 b7e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e27 b7e36
            have b7e40 : False := by grind
            exact b7e40
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b8e22 : (M.op y x) = (M.op y y) := by grind
            have b8e25 : (M.op x y) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e29 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) X0)) := by
              intro X0
              first
              | (have i₁ := b8e14 X0 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e33 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b8e29 X0
                 have i₂ := b8e14 X0 y y
                 grind)
              | exact superpose b8e14 b8e29
              | exact resolve b8e29 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29
            have b8e34 : (M.op x y) ≠ (M.op x y) := by
              first
              | (have i₁ := b8e25
                 have i₂ := b8e33 x
                 grind)
              | exact superpose b8e33 b8e25
              | (have r₁ := b8e25
                 have r₂ := b8e33 x
                 grind)
              | exact resolve b8e25 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e33
            have b8e37 : False := by grind
            exact b8e37
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b9e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b9e22 : (M.op y x) = (M.op x x) := by grind
          have b9e24 : (M.op x y) = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e21
            | exact resolve b9e21 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e30 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b9e13 X0 y x
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e34 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b9e30 X0
               have i₂ := b9e13 X0 x x
               grind)
            | exact superpose b9e13 b9e30
            | exact resolve b9e30 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30
          have b9e37 : (M.op y x) ≠ (M.op x x) := by
            first
            | (have i₁ := b9e25
               have i₂ := b9e34 y
               grind)
            | exact superpose b9e34 b9e25
            | exact resolve b9e25 b9e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e25 b9e34
          have b9e38 : False := by grind
          exact b9e38
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b10e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b10e23 : (M.op y x) = (M.op x x) := by grind
            have b10e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
            have b10e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e28 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b10e21
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e21
              | exact resolve b10e21 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e41 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X0)) := by
              intro X0
              first
              | (have i₁ := b10e14 X0 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e14
              | exact resolve b10e14 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e42 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b10e41 X0
                 have i₂ := b10e14 X0 (σ y) (σ y)
                 grind)
              | exact superpose b10e14 b10e41
              | exact resolve b10e41 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e41
            have b10e49 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e53 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b10e49
            have b10e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b10e53
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e53
              | exact resolve b10e53 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e53
            have b10e59 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b10e55
                 have i₂ := b10e42 (σ x)
                 grind)
              | exact superpose b10e42 b10e55
              | exact resolve b10e55 b10e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e42 b10e55
            have b10e69 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ (M.op X0 X0) = (k x X0) := by
              intro X0
              first
              | (have i₁ := b10e18 x X0
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e18
              | (have j0 := b10e18 x X0
                 grind)
              | (have r₁ := b10e18 x y
                 have r₂ := b10e23
                 grind)
              | exact resolve b10e18 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e164 : (σ (M.op y y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b10e28
                 have i₂ := b10e59
                 grind)
              | exact superpose b10e59 b10e28
              | exact resolve b10e28 b10e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e28 b10e59
            have b10e271 : (M.op y x) = (M.op y y) ∨ (M.op y y) = (k x y) := by
              first
              | (have j0 := b10e69 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e69
            have b10e272 : (M.op y y) = (k x y) := by
              first
              | (have r₁ := b10e271
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e271 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e271
            have b10e274 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b10e164
                 have i₂ := b10e272
                 grind)
              | exact superpose b10e272 b10e164
              | exact resolve b10e164 b10e272
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e164 b10e272
            have b10e277 : False := by grind
            exact b10e277
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b11e23 : (M.op y x) = (M.op x x) := by grind
            have b11e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e38 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X0)) := by
              intro X0
              first
              | (have i₁ := b11e14 X0 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e14
              | exact resolve b11e14 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e39 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b11e38 X0
                 have i₂ := b11e14 X0 (σ y) (σ y)
                 grind)
              | exact superpose b11e14 b11e38
              | exact resolve b11e38 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e38
            have b11e46 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b11e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e50 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b11e46
            have b11e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e50
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e50
              | exact resolve b11e50 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e50
            have b11e56 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e52
                 have i₂ := b11e39 (σ x)
                 grind)
              | exact superpose b11e39 b11e52
              | exact resolve b11e52 b11e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e52
            have b11e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b11e20 X0 X0
                 have i₂ := b11e49 (σ X0)
                 grind)
              | exact superpose b11e49 b11e20
              | exact resolve b11e20 b11e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b11e58 X0
                 have i₂ := b11e49 X0
                 grind)
              | exact superpose b11e49 b11e58
              | exact resolve b11e58 b11e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e49 b11e58
            have b11e65 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ (M.op X0 X0) = (k x X0) := by
              intro X0
              first
              | (have i₁ := b11e18 x X0
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x X0
                 grind)
              | (have r₁ := b11e18 x y
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e246 : (M.op y x) = (M.op y y) ∨ (M.op y y) = (k x y) := by
              first
              | (have j0 := b11e65 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e65
            have b11e247 : (M.op y y) = (k x y) := by
              first
              | (have r₁ := b11e246
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e246 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e246
            have b11e301 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b11e39 (σ x)
                 have i₂ := b11e61 x
                 grind)
              | exact superpose b11e61 b11e39
              | exact resolve b11e39 b11e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e39 b11e61
            have b11e315 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
              first
              | (have i₁ := b11e301
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e301
              | exact resolve b11e301 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e301
            have b11e839 : (σ (k x y)) = (σ (M.op y x)) := by
              first
              | (have i₁ := b11e56
                 have i₂ := b11e315
                 grind)
              | exact superpose b11e315 b11e56
              | exact resolve b11e56 b11e315
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e56 b11e315
            have b11e848 : (σ (M.op y x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b11e839
                 have i₂ := b11e247
                 grind)
              | exact superpose b11e247 b11e839
              | exact resolve b11e839 b11e247
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e247 b11e839
            have b11e1023 : (M.op y x) = (τ (σ (M.op y y))) := by
              first
              | (have i₁ := b11e15 (M.op y x)
                 have i₂ := b11e848
                 grind)
              | exact superpose b11e848 b11e15
              | exact resolve b11e15 b11e848
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e848
            have b11e1024 : (M.op y x) = (M.op y y) := by
              first
              | (have i₁ := b11e1023
                 have i₂ := b11e15 (M.op y y)
                 grind)
              | exact superpose b11e15 b11e1023
              | exact resolve b11e1023 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1023
            have b11e1030 : False := by grind
            exact b11e1030
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b12e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b12e23 : (M.op y x) = (M.op x x) := by grind
            have b12e26 : (M.op x y) = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (M.op y y) ≠ (M.op x x) := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e22
              | exact resolve b12e22 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e33 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b12e14 X0 y x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e37 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b12e33 X0
                 have i₂ := b12e14 X0 x x
                 grind)
              | exact superpose b12e14 b12e33
              | exact resolve b12e33 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e33
            have b12e40 : (M.op y x) ≠ (M.op x x) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e37 y
                 grind)
              | exact superpose b12e37 b12e28
              | exact resolve b12e28 b12e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e37
            have b12e41 : False := by grind
            exact b12e41
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
                intro X0 X1 X2
                grind
              have b13e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b13e26 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
              have b13e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b13e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b13e25
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e25
                | exact resolve b13e25 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b13e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b13e21 X0 X0
                   have i₂ := b13e63 (σ X0)
                   grind)
                | exact superpose b13e63 b13e21
                | exact resolve b13e21 b13e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e68 X0
                   have i₂ := b13e63 X0
                   grind)
                | exact superpose b13e63 b13e68
                | exact resolve b13e68 b13e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e63 b13e68
              have b13e83 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
                intro X0
                first
                | (have i₁ := b13e19 y X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e19
                | (have j0 := b13e19 y X0
                   grind)
                | (have r₁ := b13e19 y x
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e19 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e104 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e15 X2 X0 X0
                   have i₂ := b13e20 X1 X0
                   grind)
                | (have i₁ := b13e15 X0 X0 X1
                   have i₂ := b13e20 X0 X1
                   grind)
                | exact superpose b13e20 b13e15
                | (have j1 := b13e20 X1 X0
                   grind)
                | exact resolve b13e15 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e136 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e104 X0 X1 X2
                   have i₂ := b13e15 X2 X1 X0
                   grind)
                | exact superpose b13e15 b13e104
                | (have j0 := b13e104 X0 X1 X2
                   grind)
                | exact resolve b13e104 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e104
              have b13e217 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b13e29
                   have i₂ := b13e75 y
                   grind)
                | exact superpose b13e75 b13e29
                | exact resolve b13e29 b13e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e29
              have b13e227 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b13e217
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e217
                | exact resolve b13e217 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e217
              have b13e228 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b13e227
                   have i₂ := b13e75 x
                   grind)
                | exact superpose b13e75 b13e227
                | exact resolve b13e227 b13e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e227
              have b13e239 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
                first
                | (have j0 := b13e83 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e83
              have b13e240 : (M.op x x) = (k y x) := by
                first
                | (have r₁ := b13e239
                   have r₂ := b13e27
                   grind)
                | exact resolve b13e239 b13e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e239
              have b13e757 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b13e136 X1 X0 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e8738 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b13e757 (σ y) (σ x)
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e757
                | (have j0 := b13e757 (σ y) (σ x)
                   grind)
                | exact resolve b13e757 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e757
              have b13e8792 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have j1 := b13e136 (σ x) (σ y) x
                   grind)
                | (have r₁ := b13e8738
                   have r₂ := b13e136 (σ x) (σ y) (σ x)
                   grind)
                | (have r₁ := b13e8738
                   have r₂ := b13e136 (σ y) (σ x) (σ x)
                   grind)
                | exact resolve b13e8738 b13e136
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e136 b13e8738
              have b13e8805 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b13e8792
                   have i₂ := b13e75 y
                   grind)
                | exact superpose b13e75 b13e8792
                | exact resolve b13e8792 b13e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8792
              have b13e8808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b13e8805
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e8805
                | exact resolve b13e8805 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8805
              have b13e8811 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have r₁ := b13e8808
                   have r₂ := b13e22
                   grind)
                | exact resolve b13e8808 b13e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8808
              have b13e8813 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
                first
                | (have i₁ := b13e8811
                   have i₂ := b13e21 y x
                   grind)
                | exact superpose b13e21 b13e8811
                | exact resolve b13e8811 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8811
              have b13e8814 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e8813
                   have i₂ := b13e240
                   grind)
                | exact superpose b13e240 b13e8813
                | exact resolve b13e8813 b13e240
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8813
              have b13e8827 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b13e18 (σ y) (σ x)
                   have i₂ := b13e8814
                   grind)
                | exact superpose b13e8814 b13e18
                | (have j0 := b13e18 (σ y) (σ x)
                   grind)
                | exact resolve b13e18 b13e8814
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8814
              have b13e8862 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have r₁ := b13e8827
                   have r₂ := b13e75 x
                   grind)
                | exact resolve b13e8827 b13e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8827
              have b13e8871 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
                first
                | (have i₁ := b13e8862
                   have i₂ := b13e21 y x
                   grind)
                | exact superpose b13e21 b13e8862
                | exact resolve b13e8862 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8862
              have b13e8876 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e8871
                   have i₂ := b13e240
                   grind)
                | exact superpose b13e240 b13e8871
                | exact resolve b13e8871 b13e240
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e240 b13e8871
              have b13e8881 : (σ (M.op y y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e8876
                   have i₂ := b13e75 y
                   grind)
                | exact superpose b13e75 b13e8876
                | exact resolve b13e8876 b13e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e75 b13e8876
              have b13e8885 : (σ (M.op x y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e8881
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e8881
                | exact resolve b13e8881 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8881
              have b13e8888 : False := by grind
              exact b13e8888
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b14e26 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
              have b14e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b14e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b14e25
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e25
                | exact resolve b14e25 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b14e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b14e21 X0 X0
                   have i₂ := b14e71 (σ X0)
                   grind)
                | exact superpose b14e71 b14e21
                | exact resolve b14e21 b14e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b14e74 X0
                   have i₂ := b14e71 X0
                   grind)
                | exact superpose b14e71 b14e74
                | exact resolve b14e74 b14e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e71 b14e74
              have b14e106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e18 X1 X0
                   have i₂ := b14e20 X1 X0
                   grind)
                | (have i₁ := b14e18 X1 X1
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e18
                | (have j0 := b14e18 X0 X0
                   have j1 := b14e20 X1 X0
                   grind)
                | (have r₁ := b14e18 X0 X1
                   have r₂ := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e18 X0 X0
                   have r₂ := b14e20 X0 X0
                   grind)
                | (have r₁ := b14e18 X1 X1
                   have r₂ := b14e20 X1 X1
                   grind)
                | exact resolve b14e18 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e110 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X2 X0 X0
                   have i₂ := b14e20 X1 X0
                   grind)
                | (have i₁ := b14e15 X0 X0 X1
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e15
                | (have j1 := b14e20 X1 X0
                   grind)
                | exact resolve b14e15 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e19 X0 X1
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e19 X0 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e19
                | (have j0 := b14e19 X0 X1
                   have j1 := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e19 X1 X1
                   have r₂ := b14e20 X1 X1
                   grind)
                | (have r₁ := b14e19 X0 X0
                   have r₂ := b14e20 X0 X0
                   grind)
                | (have r₁ := b14e19 X0 X1
                   have r₂ := b14e20 X0 X1
                   grind)
                | exact resolve b14e19 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e132 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b14e20 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e135 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b14e115 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e115
              have b14e137 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have j0 := b14e106 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e106
              have b14e144 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have j0 := b14e135 X0 X1
                   have j1 := b14e132 X1 X0
                   grind)
                | (have r₁ := b14e135 X0 X1
                   have r₂ := b14e132 X0 X1
                   grind)
                | (have r₁ := b14e135 X1 X0
                   have r₂ := b14e132 X0 X1
                   grind)
                | (have r₁ := b14e135 X0 X0
                   have r₂ := b14e132 X0 X0
                   grind)
                | exact resolve b14e135 b14e132
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e132 b14e135
              have b14e146 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e110 X0 X1 X2
                   have i₂ := b14e15 X2 X1 X0
                   grind)
                | exact superpose b14e15 b14e110
                | (have j0 := b14e110 X0 X1 X2
                   grind)
                | exact resolve b14e110 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e110
              have b14e157 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b14e29
                   have i₂ := b14e83 y
                   grind)
                | exact superpose b14e83 b14e29
                | exact resolve b14e29 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29
              have b14e166 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b14e157
                   have i₂ := b14e83 x
                   grind)
                | exact superpose b14e83 b14e157
                | exact resolve b14e157 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e157
              have b14e398 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e144 (σ X0) (σ X1)
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e144
                | (have j0 := b14e144 (σ X0) (σ X1)
                   grind)
                | exact resolve b14e144 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e144
              have b14e458 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e398 X0 X1
                   have i₂ := b14e83 X1
                   grind)
                | exact superpose b14e83 b14e398
                | (have j0 := b14e398 X0 X1
                   grind)
                | exact resolve b14e398 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e398
              have b14e472 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e458 X0 X1
                   have i₂ := b14e83 X1
                   grind)
                | exact superpose b14e83 b14e458
                | (have j0 := b14e458 X0 X1
                   grind)
                | exact resolve b14e458 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e458
              have b14e655 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b14e146 X1 X0 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e6328 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b14e655 (σ y) (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e655
                | (have j0 := b14e655 (σ y) (σ x)
                   grind)
                | exact resolve b14e655 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e655
              have b14e6370 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have j1 := b14e146 (σ x) (σ y) x
                   grind)
                | (have r₁ := b14e6328
                   have r₂ := b14e146 (σ x) (σ y) (σ x)
                   grind)
                | (have r₁ := b14e6328
                   have r₂ := b14e146 (σ y) (σ x) (σ x)
                   grind)
                | exact resolve b14e6328 b14e146
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e146 b14e6328
              have b14e6381 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b14e6370
                   have i₂ := b14e83 y
                   grind)
                | exact superpose b14e83 b14e6370
                | exact resolve b14e6370 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6370
              have b14e6384 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e6381
                   have i₂ := b14e21 y x
                   grind)
                | exact superpose b14e21 b14e6381
                | exact resolve b14e6381 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6381
              have b14e46349 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e19 (σ X0) (σ X1)
                   have i₂ := b14e472 X0 X1
                   grind)
                | exact superpose b14e472 b14e19
                | (have j0 := b14e19 (σ X0) (σ X1)
                   have j1 := b14e472 X0 X1
                   grind)
                | exact resolve b14e19 b14e472
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e46712 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e46349 X0 X1
                   have i₂ := b14e83 X0
                   grind)
                | exact superpose b14e83 b14e46349
                | (have j0 := b14e46349 X0 X1
                   grind)
                | exact resolve b14e46349 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e46349
              have b14e46886 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e46712 X0 X1
                   have i₂ := b14e83 X1
                   grind)
                | exact superpose b14e83 b14e46712
                | (have j0 := b14e46712 X0 X1
                   grind)
                | exact resolve b14e46712 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e46712
              have b14e46887 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have j0 := b14e46886 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e46886
              have b14e46989 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e46887 X0 X1
                   have i₂ := b14e83 X1
                   grind)
                | exact superpose b14e83 b14e46887
                | (have j0 := b14e46887 X0 X1
                   grind)
                | exact resolve b14e46887 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e83 b14e46887
              have b14e47045 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e46989 X0 X1
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e46989
                | (have j0 := b14e46989 X0 X1
                   grind)
                | exact resolve b14e46989 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e46989
              have b14e47046 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have j0 := b14e47045 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e47045
              have b14e79740 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e6384
                   grind)
                | exact superpose b14e6384 b14e22
                | exact resolve b14e22 b14e6384
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6384
              have b14e81411 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b14e79740
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e79740
                | (have j1 := b14e20 y x
                   grind)
                | exact resolve b14e79740 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e79740
              have b14e81417 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
              clear b14e81411
              have b14e81421 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have r₁ := b14e81417
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e81417 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e81417
              have b14e81422 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have r₁ := b14e81421
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e81421 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e81421
              have b14e82688 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
                first
                | (have i₁ := b14e81422
                   have i₂ := b14e472 y x
                   grind)
                | exact superpose b14e472 b14e81422
                | (have j1 := b14e472 y x
                   grind)
                | exact resolve b14e81422 b14e472
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e472
              have b14e82752 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
                first
                | (have j1 := b14e47046 y x
                   grind)
                | (have r₁ := b14e82688
                   have r₂ := b14e47046 y x
                   grind)
                | exact resolve b14e82688 b14e47046
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e47046 b14e82688
              have b14e82755 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
                first
                | (have i₁ := b14e82752
                   have i₂ := b14e81422
                   grind)
                | exact superpose b14e81422 b14e82752
                | exact resolve b14e82752 b14e81422
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e81422 b14e82752
              have b14e82757 : (σ (M.op x x)) = (σ (k y x)) := by
                first
                | (have r₁ := b14e82755
                   have r₂ := b14e166
                   grind)
                | exact resolve b14e82755 b14e166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e82755
              have b14e83235 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b14e82757
                   have i₂ := b14e137 x y
                   grind)
                | exact superpose b14e137 b14e82757
                | (have j1 := b14e137 x y
                   grind)
                | exact resolve b14e82757 b14e137
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e137
              have b14e83247 : (k y x) = (τ (σ (M.op x x))) := by
                first
                | (have i₁ := b14e16 (k y x)
                   have i₂ := b14e82757
                   grind)
                | exact superpose b14e82757 b14e16
                | exact resolve b14e16 b14e82757
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e82757
              have b14e83299 : (M.op x x) = (k y x) := by
                first
                | (have i₁ := b14e83247
                   have i₂ := b14e16 (M.op x x)
                   grind)
                | exact superpose b14e16 b14e83247
                | exact resolve b14e83247 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e83247
              have b14e83303 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have r₁ := b14e83235
                   have r₂ := b14e166
                   grind)
                | exact resolve b14e83235 b14e166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e166 b14e83235
              have b14e83305 : (M.op x y) = (k y x) := by
                first
                | (have r₁ := b14e83303
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e83303 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e83303
              have b14e83307 : (M.op x y) = (M.op x x) := by
                first
                | (have i₁ := b14e83305
                   have i₂ := b14e83299
                   grind)
                | exact superpose b14e83299 b14e83305
                | exact resolve b14e83305 b14e83299
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e83299 b14e83305
              have b14e83308 : False := by grind
              exact b14e83308
        · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b15e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b15e23 : (M.op y x) = (M.op x x) := by grind
            have b15e26 : (M.op x y) = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : (M.op y y) ≠ (M.op x x) := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e22
              | exact resolve b15e22 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e32 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b15e14 X0 y x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e36 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b15e32 X0
                 have i₂ := b15e14 X0 x x
                 grind)
              | exact superpose b15e14 b15e32
              | exact resolve b15e32 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e32
            have b15e39 : (M.op y x) ≠ (M.op x x) := by
              first
              | (have i₁ := b15e27
                 have i₂ := b15e36 y
                 grind)
              | exact superpose b15e36 b15e27
              | exact resolve b15e27 b15e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27 b15e36
            have b15e40 : False := by grind
            exact b15e40
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b16e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e24 : (M.op y x) = (M.op x x) := by grind
              have b16e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b16e26 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
              have b16e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b16e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b16e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b16e21 X0 X0
                   have i₂ := b16e61 (σ X0)
                   grind)
                | exact superpose b16e61 b16e21
                | exact resolve b16e21 b16e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b16e66 X0
                   have i₂ := b16e61 X0
                   grind)
                | exact superpose b16e61 b16e66
                | exact resolve b16e66 b16e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e61 b16e66
              have b16e79 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
                first
                | (have i₁ := b16e19 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x x
                   grind)
                | (have r₁ := b16e19 x y
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e82 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
              clear b16e79
              have b16e83 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
                first
                | (have i₁ := b16e82
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e82
                | exact resolve b16e82 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e82
              have b16e84 : (M.op y y) = (k x y) := by
                first
                | (have r₁ := b16e83
                   have r₂ := b16e27
                   grind)
                | exact resolve b16e83 b16e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e83
              have b16e85 : (M.op x y) = (k x y) := by
                first
                | (have i₁ := b16e84
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e84
                | exact resolve b16e84 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e84
              have b16e100 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b16e25
                   have i₂ := b16e20 X0 (σ y)
                   grind)
                | (have i₁ := b16e25
                   have i₂ := b16e20 (σ y) (σ y)
                   grind)
                | exact superpose b16e20 b16e25
                | (have j1 := b16e20 X0 (σ y)
                   grind)
                | (have r₁ := b16e25
                   have r₂ := b16e20 (σ x) (σ y)
                   grind)
                | exact resolve b16e25 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e206 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b16e25
                   have i₂ := b16e73 y
                   grind)
                | exact superpose b16e73 b16e25
                | exact resolve b16e25 b16e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e73
              have b16e216 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e206
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e206
                | exact resolve b16e206 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e206
              have b16e1194 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b16e100 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e100
              have b16e1195 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b16e1194
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e1194 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e1194
              have b16e1203 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b16e1195
                   have i₂ := b16e21 x y
                   grind)
                | exact superpose b16e21 b16e1195
                | exact resolve b16e1195 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e1195
              have b16e1204 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e1203
                   have i₂ := b16e85
                   grind)
                | exact superpose b16e85 b16e1203
                | exact resolve b16e1203 b16e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e85 b16e1203
              have b16e1205 : False := by grind
              exact b16e1205
            · have b17e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : (M.op y x) ≠ (M.op y y) := by grind
              have b17e24 : (M.op y x) = (M.op x x) := by grind
              have b17e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b17e26 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : (M.op y y) ≠ (M.op x x) := by
                first
                | (have i₁ := b17e23
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e23
                | exact resolve b17e23 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b17e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b17e21 X0 X0
                   have i₂ := b17e69 (σ X0)
                   grind)
                | exact superpose b17e69 b17e21
                | exact resolve b17e21 b17e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e72 X0
                   have i₂ := b17e69 X0
                   grind)
                | exact superpose b17e69 b17e72
                | exact resolve b17e72 b17e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e69 b17e72
              have b17e89 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
                first
                | (have i₁ := b17e19 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x x
                   grind)
                | (have r₁ := b17e19 x y
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e91 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
              clear b17e89
              have b17e92 : (M.op y y) = (k x y) := by
                first
                | (have r₁ := b17e91
                   have r₂ := b17e29
                   grind)
                | exact resolve b17e91 b17e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e29 b17e91
              have b17e107 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b17e25
                   have i₂ := b17e20 X0 (σ y)
                   grind)
                | (have i₁ := b17e25
                   have i₂ := b17e20 (σ y) (σ y)
                   grind)
                | exact superpose b17e20 b17e25
                | (have j1 := b17e20 X0 (σ y)
                   grind)
                | (have r₁ := b17e25
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e25 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e148 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b17e25
                   have i₂ := b17e81 y
                   grind)
                | exact superpose b17e81 b17e25
                | exact resolve b17e25 b17e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e81
              have b17e1130 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b17e107 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e107
              have b17e1131 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e1130
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e1130 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1130
              have b17e1139 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e1131
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e1131
                | exact resolve b17e1131 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1131
              have b17e1140 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b17e1139
                   have i₂ := b17e92
                   grind)
                | exact superpose b17e92 b17e1139
                | exact resolve b17e1139 b17e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e92 b17e1139
              have b17e1141 : False := by grind
              exact b17e1141
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b18e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b18e24 : (M.op x y) = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X0)) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 y x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e32 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b18e28 X0
               have i₂ := b18e13 X0 x x
               grind)
            | exact superpose b18e13 b18e28
            | exact resolve b18e28 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e28
          have b18e35 : (M.op y x) ≠ (M.op y x) := by
            first
            | (have i₁ := b18e21
               have i₂ := b18e32 y
               grind)
            | exact superpose b18e32 b18e21
            | (have r₁ := b18e21
               have r₂ := b18e32 y
               grind)
            | exact resolve b18e21 b18e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e32
          have b18e36 : False := by grind
          exact b18e36
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b19e23 : (M.op y x) ≠ (M.op x x) := by grind
            have b19e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e47 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X0)) := by
              intro X0
              first
              | (have i₁ := b19e14 X0 (σ x) (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e14
              | exact resolve b19e14 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e48 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b19e47 X0
                 have i₂ := b19e14 X0 (σ y) (σ y)
                 grind)
              | exact superpose b19e14 b19e47
              | exact resolve b19e47 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e47
            have b19e54 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b19e17 (σ x) (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e17
              | (have j0 := b19e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b19e17 (σ x) (σ y)
                 have r₂ := b19e24
                 grind)
              | exact resolve b19e17 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b19e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e57 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b19e54
            have b19e58 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b19e57
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e57
              | exact resolve b19e57 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e57
            have b19e61 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b19e58
                 have i₂ := b19e48 (σ x)
                 grind)
              | exact superpose b19e48 b19e58
              | exact resolve b19e58 b19e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e58
            have b19e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b19e20 X0 X0
                 have i₂ := b19e56 (σ X0)
                 grind)
              | exact superpose b19e56 b19e20
              | exact resolve b19e20 b19e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b19e63 X0
                 have i₂ := b19e56 X0
                 grind)
              | exact superpose b19e56 b19e63
              | exact resolve b19e63 b19e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e56 b19e63
            have b19e431 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b19e48 (σ x)
                 have i₂ := b19e68 x
                 grind)
              | exact superpose b19e68 b19e48
              | exact resolve b19e48 b19e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e48 b19e68
            have b19e859 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b19e61
                 have i₂ := b19e431
                 grind)
              | exact superpose b19e431 b19e61
              | exact resolve b19e61 b19e431
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e61 b19e431
            have b19e949 : (k x y) = (τ (σ (M.op x x))) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e859
                 grind)
              | exact superpose b19e859 b19e15
              | exact resolve b19e15 b19e859
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e859
            have b19e950 : (M.op x x) = (k x y) := by
              first
              | (have i₁ := b19e949
                 have i₂ := b19e15 (M.op x x)
                 grind)
              | exact superpose b19e15 b19e949
              | exact resolve b19e949 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e949
            have b19e1048 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
              first
              | (have i₁ := b19e19 x y
                 have i₂ := b19e950
                 grind)
              | exact superpose b19e950 b19e19
              | (have j0 := b19e19 x y
                 grind)
              | exact resolve b19e19 b19e950
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e950
            have b19e1049 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
            clear b19e1048
            have b19e1053 : (M.op y x) = (M.op y y) := by
              first
              | (have r₁ := b19e1049
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e1049 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1049
            have b19e1060 : False := by grind
            exact b19e1060
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b20e23 : (M.op y x) ≠ (M.op x x) := by grind
            have b20e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e44 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X0)) := by
              intro X0
              first
              | (have i₁ := b20e14 X0 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14
              | exact resolve b20e14 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e45 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e44 X0
                 have i₂ := b20e14 X0 (σ y) (σ y)
                 grind)
              | exact superpose b20e14 b20e44
              | exact resolve b20e44 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e44
            have b20e51 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b20e17 (σ x) (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b20e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b20e51
            have b20e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b20e54
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e54
              | exact resolve b20e54 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e54
            have b20e58 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b20e55
                 have i₂ := b20e45 (σ x)
                 grind)
              | exact superpose b20e45 b20e55
              | exact resolve b20e55 b20e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e55
            have b20e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 X0
                 have i₂ := b20e53 (σ X0)
                 grind)
              | exact superpose b20e53 b20e20
              | exact resolve b20e20 b20e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e60 X0
                 have i₂ := b20e53 X0
                 grind)
              | exact superpose b20e53 b20e60
              | exact resolve b20e60 b20e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e53 b20e60
            have b20e348 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b20e45 (σ x)
                 have i₂ := b20e65 x
                 grind)
              | exact superpose b20e65 b20e45
              | exact resolve b20e45 b20e65
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e45 b20e65
            have b20e757 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b20e58
                 have i₂ := b20e348
                 grind)
              | exact superpose b20e348 b20e58
              | exact resolve b20e58 b20e348
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e58 b20e348
            have b20e868 : (k x y) = (τ (σ (M.op x x))) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e757
                 grind)
              | exact superpose b20e757 b20e15
              | exact resolve b20e15 b20e757
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e757
            have b20e869 : (M.op x x) = (k x y) := by
              first
              | (have i₁ := b20e868
                 have i₂ := b20e15 (M.op x x)
                 grind)
              | exact superpose b20e15 b20e868
              | exact resolve b20e868 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e868
            have b20e949 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
              first
              | (have i₁ := b20e19 x y
                 have i₂ := b20e869
                 grind)
              | exact superpose b20e869 b20e19
              | (have j0 := b20e19 x y
                 grind)
              | exact resolve b20e19 b20e869
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e869
            have b20e950 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
            clear b20e949
            have b20e954 : (M.op y x) = (M.op y y) := by
              first
              | (have r₁ := b20e950
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e950 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e950
            have b20e961 : False := by grind
            exact b20e961
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b21e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b21e26 : (M.op x y) = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e31 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X0)) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 y x
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e35 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b21e31 X0
                 have i₂ := b21e14 X0 x x
                 grind)
              | exact superpose b21e14 b21e31
              | exact resolve b21e31 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e31
            have b21e38 : (M.op y x) ≠ (M.op y x) := by
              first
              | (have i₁ := b21e22
                 have i₂ := b21e35 y
                 grind)
              | exact superpose b21e35 b21e22
              | (have r₁ := b21e22
                 have r₂ := b21e35 y
                 grind)
              | exact resolve b21e22 b21e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e35
            have b21e39 : False := by grind
            exact b21e39
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : (M.op y x) ≠ (M.op y y) := by grind
              have b22e24 : (M.op y x) ≠ (M.op x x) := by grind
              have b22e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b22e26 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
              have b22e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e29 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b22e25
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e25
                | exact resolve b22e25 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e30 : (M.op x y) ≠ (M.op y x) := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e23
                | exact resolve b22e23 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b22e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b22e21 X0 X0
                   have i₂ := b22e73 (σ X0)
                   grind)
                | exact superpose b22e73 b22e21
                | exact resolve b22e21 b22e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b22e78 X0
                   have i₂ := b22e73 X0
                   grind)
                | exact superpose b22e73 b22e78
                | exact resolve b22e78 b22e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e73 b22e78
              have b22e95 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b22e19 (σ x) (σ y)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e19
                | (have j0 := b22e19 (σ x) (σ x)
                   grind)
                | (have r₁ := b22e19 (σ x) (σ y)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e19 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e98 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
              clear b22e95
              have b22e99 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e98
                   have r₂ := b22e29
                   grind)
                | exact resolve b22e98 b22e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e29 b22e98
              have b22e100 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b22e99
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e99
                | exact resolve b22e99 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e99
              have b22e101 : (σ (k x y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b22e100
                   have i₂ := b22e87 y
                   grind)
                | exact superpose b22e87 b22e100
                | exact resolve b22e100 b22e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e87 b22e100
              have b22e102 : (σ (M.op x y)) = (σ (k x y)) := by
                first
                | (have i₁ := b22e101
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e101
                | exact resolve b22e101 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e101
              have b22e107 : (k x y) = (τ (σ (M.op x y))) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e102
                   grind)
                | exact superpose b22e102 b22e16
                | exact resolve b22e16 b22e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e102
              have b22e108 : (M.op x y) = (k x y) := by
                first
                | (have i₁ := b22e107
                   have i₂ := b22e16 (M.op x y)
                   grind)
                | exact superpose b22e16 b22e107
                | exact resolve b22e107 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e107
              have b22e166 : (M.op x y) = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e108
                   grind)
                | exact superpose b22e108 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e108
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e108
              have b22e167 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
                first
                | (have r₁ := b22e166
                   have r₂ := b22e30
                   grind)
                | exact resolve b22e166 b22e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e166
              have b22e169 : (M.op y x) = (M.op y y) := by
                first
                | (have r₁ := b22e167
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e167 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e167
              have b22e171 : (M.op x y) = (M.op y x) := by
                first
                | (have i₁ := b22e169
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e169
                | exact resolve b22e169 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e169
              have b22e173 : False := by grind
              exact b22e173
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : (M.op y x) ≠ (M.op y y) := by grind
              have b23e24 : (M.op y x) ≠ (M.op x x) := by grind
              have b23e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b23e26 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b23e25
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e25
                | exact resolve b23e25 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b23e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 X0
                   have i₂ := b23e69 (σ X0)
                   grind)
                | exact superpose b23e69 b23e21
                | exact resolve b23e21 b23e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b23e72 X0
                   have i₂ := b23e69 X0
                   grind)
                | exact superpose b23e69 b23e72
                | exact resolve b23e72 b23e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e69 b23e72
              have b23e89 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b23e19 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e19
                | (have j0 := b23e19 (σ x) (σ x)
                   grind)
                | (have r₁ := b23e19 (σ x) (σ y)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e19 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e91 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
              clear b23e89
              have b23e92 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e91
                   have r₂ := b23e29
                   grind)
                | exact resolve b23e91 b23e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29 b23e91
              have b23e93 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b23e92
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e92
                | exact resolve b23e92 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e92
              have b23e94 : (σ (k x y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b23e93
                   have i₂ := b23e81 y
                   grind)
                | exact superpose b23e81 b23e93
                | exact resolve b23e93 b23e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e81 b23e93
              have b23e99 : (k x y) = (τ (σ (M.op y y))) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e94
                   grind)
                | exact superpose b23e94 b23e16
                | exact resolve b23e16 b23e94
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e94
              have b23e100 : (M.op y y) = (k x y) := by
                first
                | (have i₁ := b23e99
                   have i₂ := b23e16 (M.op y y)
                   grind)
                | exact superpose b23e16 b23e99
                | exact resolve b23e99 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e99
              have b23e157 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e100
                   grind)
                | exact superpose b23e100 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e100
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e100
              have b23e158 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by grind
              clear b23e157
              have b23e160 : (M.op y x) = (M.op x x) := by
                first
                | (have r₁ := b23e158
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e158 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e158
              have b23e162 : False := by grind
              exact b23e162
        · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have b24e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b24e26 : (M.op x y) = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e30 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X0)) := by
              intro X0
              first
              | (have i₁ := b24e14 X0 y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e34 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b24e30 X0
                 have i₂ := b24e14 X0 x x
                 grind)
              | exact superpose b24e14 b24e30
              | exact resolve b24e30 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e30
            have b24e37 : (M.op y x) ≠ (M.op y x) := by
              first
              | (have i₁ := b24e22
                 have i₂ := b24e34 y
                 grind)
              | exact superpose b24e34 b24e22
              | (have r₁ := b24e22
                 have r₂ := b24e34 y
                 grind)
              | exact resolve b24e22 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e34
            have b24e38 : False := by grind
            exact b24e38
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
                intro X0 X1 X2
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b25e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b25e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b25e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b25e21 X0 X0
                   have i₂ := b25e71 (σ X0)
                   grind)
                | exact superpose b25e71 b25e21
                | exact resolve b25e21 b25e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e76 X0
                   have i₂ := b25e71 X0
                   grind)
                | exact superpose b25e71 b25e76
                | exact resolve b25e76 b25e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e71 b25e76
              have b25e93 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
                intro X0
                first
                | (have i₁ := b25e19 y X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e19
                | (have j0 := b25e19 y X0
                   grind)
                | (have r₁ := b25e19 y x
                   have r₂ := b25e28
                   grind)
                | exact resolve b25e19 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e102 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e18 X1 (σ X0)
                   have i₂ := b25e85 X0
                   grind)
                | exact superpose b25e85 b25e18
                | (have j0 := b25e18 X1 (σ X0)
                   grind)
                | exact resolve b25e18 b25e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e117 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X2 X0 X0
                   have i₂ := b25e20 X1 X0
                   grind)
                | (have i₁ := b25e15 X0 X0 X1
                   have i₂ := b25e20 X0 X1
                   grind)
                | exact superpose b25e20 b25e15
                | (have j1 := b25e20 X1 X0
                   grind)
                | exact resolve b25e15 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e134 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e147 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e134 X0 X1
                   have i₂ := b25e85 X0
                   grind)
                | exact superpose b25e85 b25e134
                | (have j0 := b25e134 X0 X1
                   grind)
                | exact resolve b25e134 b25e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e134
              have b25e150 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e117 X0 X1 X2
                   have i₂ := b25e15 X2 X1 X0
                   grind)
                | exact superpose b25e15 b25e117
                | (have j0 := b25e117 X0 X1 X2
                   grind)
                | exact resolve b25e117 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e117
              have b25e154 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e147 X0 X1
                   have i₂ := b25e85 X1
                   grind)
                | exact superpose b25e85 b25e147
                | (have j0 := b25e147 X0 X1
                   grind)
                | exact resolve b25e147 b25e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e147
              have b25e252 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
                first
                | (have j0 := b25e93 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e93
              have b25e253 : (M.op x x) = (k y x) := by
                first
                | (have r₁ := b25e252
                   have r₂ := b25e27
                   grind)
                | exact resolve b25e252 b25e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e252
              have b25e777 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b25e25
                   have i₂ := b25e150 X0 (σ y) (σ y)
                   grind)
                | (have i₁ := b25e25
                   have i₂ := b25e150 (σ y) x (σ y)
                   grind)
                | exact superpose b25e150 b25e25
                | (have j1 := b25e150 X0 (σ y) x
                   grind)
                | (have r₁ := b25e25
                   have r₂ := b25e150 (σ y) (σ x) (σ y)
                   grind)
                | (have r₁ := b25e25
                   have r₂ := b25e150 (σ x) (σ y) (σ y)
                   grind)
                | exact resolve b25e25 b25e150
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e150
              have b25e898 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (σ y)) ∨ (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b25e777 X0
                   have i₂ := b25e85 y
                   grind)
                | exact superpose b25e85 b25e777
                | (have j0 := b25e777 X0
                   grind)
                | exact resolve b25e777 b25e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e777
              have b25e924 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b25e898 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e898
                | (have j0 := b25e898 X0
                   grind)
                | exact resolve b25e898 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e898
              have b25e1742 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e18 (σ X0) (σ X1)
                   have i₂ := b25e154 X1 X0
                   grind)
                | exact superpose b25e154 b25e18
                | (have j0 := b25e18 (σ X0) (σ X1)
                   have j1 := b25e154 X1 X0
                   grind)
                | exact resolve b25e18 b25e154
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e154
              have b25e1803 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b25e1742 X0 X1
                   have j1 := b25e102 X1 (σ X0)
                   grind)
                | (have r₁ := b25e1742 X0 X0
                   have r₂ := b25e102 X0 (σ X0)
                   grind)
                | (have r₁ := b25e1742 X0 X0
                   have r₂ := b25e102 X0 (σ X0)
                   grind)
                | exact resolve b25e1742 b25e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e102 b25e1742
              have b25e1870 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e1803 X0 X1
                   have i₂ := b25e85 X1
                   grind)
                | exact superpose b25e85 b25e1803
                | (have j0 := b25e1803 X0 X1
                   grind)
                | exact resolve b25e1803 b25e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1803
              have b25e1907 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e1870 X0 X1
                   have i₂ := b25e85 X0
                   grind)
                | exact superpose b25e85 b25e1870
                | (have j0 := b25e1870 X0 X1
                   grind)
                | exact resolve b25e1870 b25e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e85 b25e1870
              have b25e1928 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e1907 X0 X1
                   have i₂ := b25e21 X0 X1
                   grind)
                | exact superpose b25e21 b25e1907
                | (have j0 := b25e1907 X0 X1
                   grind)
                | exact resolve b25e1907 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1907
              have b25e34511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have j0 := b25e924 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e924
              have b25e34516 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have r₁ := b25e34511
                   have r₂ := b25e22
                   grind)
                | exact resolve b25e34511 b25e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34511
              have b25e34583 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
                first
                | (have i₁ := b25e34516
                   have i₂ := b25e21 y x
                   grind)
                | exact superpose b25e21 b25e34516
                | exact resolve b25e34516 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34516
              have b25e34644 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b25e34583
                   have i₂ := b25e253
                   grind)
                | exact superpose b25e253 b25e34583
                | exact resolve b25e34583 b25e253
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34583
              have b25e34698 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e34644
                   grind)
                | exact superpose b25e34644 b25e22
                | exact resolve b25e22 b25e34644
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34644
              have b25e34849 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b25e1928 y x
                   have i₂ := b25e253
                   grind)
                | exact superpose b25e253 b25e1928
                | (have j0 := b25e1928 y x
                   grind)
                | exact resolve b25e1928 b25e253
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e253 b25e1928
              have b25e34917 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
              clear b25e34849
              have b25e34940 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b25e34917
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e34917
                | exact resolve b25e34917 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34917
              have b25e34966 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have r₁ := b25e34940
                   have r₂ := b25e34698
                   grind)
                | exact resolve b25e34940 b25e34698
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34698 b25e34940
              have b25e34987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e34966
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e34966
                | exact resolve b25e34966 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34966
              have b25e34997 : False := by grind
              exact b25e34997
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b26e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b26e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 X0
                   have i₂ := b26e67 (σ X0)
                   grind)
                | exact superpose b26e67 b26e21
                | exact resolve b26e21 b26e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e70 X0
                   have i₂ := b26e67 X0
                   grind)
                | exact superpose b26e67 b26e70
                | exact resolve b26e70 b26e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e67 b26e70
              have b26e95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X1 (σ X0)
                   have i₂ := b26e79 X0
                   grind)
                | exact superpose b26e79 b26e18
                | (have j0 := b26e18 X1 (σ X0)
                   grind)
                | exact resolve b26e18 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X1 X0
                   have i₂ := b26e20 X1 X0
                   grind)
                | (have i₁ := b26e18 X1 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e18
                | (have j0 := b26e18 X0 X0
                   have j1 := b26e20 X1 X0
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 X0
                   have r₂ := b26e20 X0 X0
                   grind)
                | (have r₁ := b26e18 X1 X1
                   have r₂ := b26e20 X1 X1
                   grind)
                | exact resolve b26e18 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e109 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X2 X0 X0
                   have i₂ := b26e20 X1 X0
                   grind)
                | (have i₁ := b26e15 X0 X0 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e15
                | (have j1 := b26e20 X1 X0
                   grind)
                | exact resolve b26e15 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e19 X0 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e19 X0 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e19
                | (have j0 := b26e19 X0 X1
                   have j1 := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e19 X1 X1
                   have r₂ := b26e20 X1 X1
                   grind)
                | (have r₁ := b26e19 X0 X0
                   have r₂ := b26e20 X0 X0
                   grind)
                | (have r₁ := b26e19 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | exact resolve b26e19 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e131 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e20 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e132 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e20 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e134 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e115 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e115
              have b26e136 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e105 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e105
              have b26e141 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e134 X0 X1
                   have j1 := b26e132 X1 X0
                   grind)
                | (have r₁ := b26e134 X0 X1
                   have r₂ := b26e132 X0 X1
                   grind)
                | (have r₁ := b26e134 X1 X0
                   have r₂ := b26e132 X0 X1
                   grind)
                | (have r₁ := b26e134 X0 X0
                   have r₂ := b26e132 X0 X0
                   grind)
                | exact resolve b26e134 b26e132
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e132 b26e134
              have b26e142 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e109 X0 X1 X2
                   have i₂ := b26e15 X2 X1 X0
                   grind)
                | exact superpose b26e15 b26e109
                | (have j0 := b26e109 X0 X1 X2
                   grind)
                | exact resolve b26e109 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e109
              have b26e401 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e141 (σ X0) (σ X1)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e141
                | (have j0 := b26e141 (σ X0) (σ X1)
                   grind)
                | exact resolve b26e141 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e141
              have b26e465 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e401 X0 X1
                   have i₂ := b26e79 X1
                   grind)
                | exact superpose b26e79 b26e401
                | (have j0 := b26e401 X0 X1
                   grind)
                | exact resolve b26e401 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e401
              have b26e478 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e465 X0 X1
                   have i₂ := b26e79 X1
                   grind)
                | exact superpose b26e79 b26e465
                | (have j0 := b26e465 X0 X1
                   grind)
                | exact resolve b26e465 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e465
              have b26e641 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e142 X0 (σ y) (σ y)
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e142 (σ y) x (σ y)
                   grind)
                | exact superpose b26e142 b26e25
                | (have j1 := b26e142 X0 (σ y) x
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e142 (σ y) (σ x) (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e142 (σ x) (σ y) (σ y)
                   grind)
                | exact resolve b26e25 b26e142
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e142
              have b26e748 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (σ (M.op y y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b26e641 X0
                   have i₂ := b26e79 y
                   grind)
                | exact superpose b26e79 b26e641
                | (have j0 := b26e641 X0
                   grind)
                | exact resolve b26e641 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e641
              have b26e29510 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have j0 := b26e748 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e748
              have b26e29515 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e29510
                   have i₂ := b26e21 y x
                   grind)
                | exact superpose b26e21 b26e29510
                | exact resolve b26e29510 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29510
              have b26e38271 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e19 (σ X0) (σ X1)
                   have i₂ := b26e478 X0 X1
                   grind)
                | exact superpose b26e478 b26e19
                | (have j0 := b26e19 (σ X0) (σ X1)
                   have j1 := b26e478 X0 X1
                   grind)
                | exact resolve b26e19 b26e478
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e38599 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e38271 X0 X1
                   have i₂ := b26e79 X0
                   grind)
                | exact superpose b26e79 b26e38271
                | (have j0 := b26e38271 X0 X1
                   grind)
                | exact resolve b26e38271 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38271
              have b26e38756 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e38599 X0 X1
                   have i₂ := b26e79 X1
                   grind)
                | exact superpose b26e79 b26e38599
                | (have j0 := b26e38599 X0 X1
                   grind)
                | exact resolve b26e38599 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38599
              have b26e38757 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b26e38756 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38756
              have b26e38850 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e38757 X0 X1
                   have i₂ := b26e79 X1
                   grind)
                | exact superpose b26e79 b26e38757
                | (have j0 := b26e38757 X0 X1
                   grind)
                | exact resolve b26e38757 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38757
              have b26e38900 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e38850 X0 X1
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e38850
                | (have j0 := b26e38850 X0 X1
                   grind)
                | exact resolve b26e38850 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38850
              have b26e38901 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b26e38900 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38900
              have b26e103211 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e29515
                   grind)
                | exact superpose b26e29515 b26e22
                | exact resolve b26e22 b26e29515
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29515
              have b26e103357 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b26e103211
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e103211
                | (have j1 := b26e20 y x
                   grind)
                | exact resolve b26e103211 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103211
              have b26e103363 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
              clear b26e103357
              have b26e103367 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have r₁ := b26e103363
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e103363 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103363
              have b26e103368 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have r₁ := b26e103367
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e103367 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103367
              have b26e103489 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
                first
                | (have i₁ := b26e103368
                   have i₂ := b26e478 y x
                   grind)
                | exact superpose b26e478 b26e103368
                | (have j1 := b26e478 y x
                   grind)
                | exact resolve b26e103368 b26e478
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e478
              have b26e103496 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e103368
                   grind)
                | exact superpose b26e103368 b26e22
                | exact resolve b26e22 b26e103368
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e103501 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b26e95 x (σ y)
                   have i₂ := b26e103368
                   grind)
                | exact superpose b26e103368 b26e95
                | (have j0 := b26e95 x (σ y)
                   grind)
                | exact resolve b26e95 b26e103368
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e95
              have b26e103552 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b26e103501
                   have i₂ := b26e21 y x
                   grind)
                | exact superpose b26e21 b26e103501
                | exact resolve b26e103501 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103501
              have b26e103555 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
                first
                | (have j1 := b26e38901 y x
                   grind)
                | (have r₁ := b26e103489
                   have r₂ := b26e38901 y x
                   grind)
                | exact resolve b26e103489 b26e38901
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38901 b26e103489
              have b26e103559 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (k y x)) := by
                first
                | (have i₁ := b26e103552
                   have i₂ := b26e79 y
                   grind)
                | exact superpose b26e79 b26e103552
                | exact resolve b26e103552 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e79 b26e103552
              have b26e103560 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b26e103555
                   have i₂ := b26e103368
                   grind)
                | exact superpose b26e103368 b26e103555
                | exact resolve b26e103555 b26e103368
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103368 b26e103555
              have b26e108480 : (k y x) = (τ (σ (M.op x x))) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b26e16 (k y x)
                   have i₂ := b26e103560
                   grind)
                | exact superpose b26e103560 b26e16
                | exact resolve b26e16 b26e103560
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103560
              have b26e108524 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
                first
                | (have i₁ := b26e108480
                   have i₂ := b26e16 (M.op x x)
                   grind)
                | exact superpose b26e16 b26e108480
                | exact resolve b26e108480 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e108480
              have b26e109859 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (k y x) := by
                first
                | (have i₁ := b26e16 (M.op y y)
                   have i₂ := b26e108524
                   grind)
                | exact superpose b26e108524 b26e16
                | exact resolve b26e16 b26e108524
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e108524
              have b26e109906 : (M.op x x) = (k y x) ∨ (M.op y y) = (M.op x x) := by
                first
                | (have i₁ := b26e109859
                   have i₂ := b26e16 (M.op x x)
                   grind)
                | exact superpose b26e16 b26e109859
                | exact resolve b26e109859 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e109859
              have b26e110060 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b26e109906
                   have i₂ := b26e136 x y
                   grind)
                | exact superpose b26e136 b26e109906
                | (have j1 := b26e136 x y
                   grind)
                | exact resolve b26e109906 b26e136
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e110068 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) := by
                first
                | (have i₁ := b26e136 x y
                   have i₂ := b26e109906
                   grind)
                | exact superpose b26e109906 b26e136
                | (have j0 := b26e136 x y
                   grind)
                | exact resolve b26e136 b26e109906
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e136 b26e109906
              have b26e110088 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
              clear b26e110068
              have b26e110093 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
              clear b26e110060
              have b26e110100 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have r₁ := b26e110088
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e110088 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e110088
              have b26e110104 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have j1 := b26e131 x y
                   grind)
                | (have r₁ := b26e110093
                   have r₂ := b26e131 x y
                   grind)
                | (have r₁ := b26e110093
                   have r₂ := b26e131 y x
                   grind)
                | exact resolve b26e110093 b26e131
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e131 b26e110093
              have b26e110110 : (M.op y y) = (M.op x x) := by
                first
                | (have r₁ := b26e110100
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e110100 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e110100
              have b26e110114 : (M.op x y) = (k y x) := by
                first
                | (have r₁ := b26e110104
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e110104 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e110104
              have b26e111992 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b26e103496
                   have i₂ := b26e110110
                   grind)
                | exact superpose b26e110110 b26e103496
                | exact resolve b26e103496 b26e110110
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103496
              have b26e111993 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
                first
                | (have i₁ := b26e103559
                   have i₂ := b26e110110
                   grind)
                | exact superpose b26e110110 b26e103559
                | exact resolve b26e103559 b26e110110
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103559 b26e110110
              have b26e112121 : (σ (M.op x x)) = (σ (k y x)) := by grind
              clear b26e111993
              have b26e112150 : (σ (M.op x y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b26e112121
                   have i₂ := b26e110114
                   grind)
                | exact superpose b26e110114 b26e112121
                | exact resolve b26e112121 b26e110114
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e110114 b26e112121
              have b26e112152 : False := by grind
              exact b26e112152

/-- `Equation4383`: `x ◇ (x ◇ x) = (x ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pxy_y_pxy_Equation4383 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4383 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4383.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e22
        | exact resolve b0e22 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X1) := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e32 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 X2
             have i₂ := b1e12 X0 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (M.op X0 X0)
             have i₂ := b1e12 X0 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e12 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : (M.op x (M.op x x)) = (M.op y y) := by
          first
          | (have i₁ := b1e12 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : (M.op y y) = (M.op (M.op y y) (M.op x x)) := by
          first
          | (have i₁ := b1e12 x (M.op x x)
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e12
          | exact resolve b1e12 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e39 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y y)) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e39
          | exact resolve b1e39 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e66 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e67 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X2
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e12 X0 X1
             have i₂ := b1e17 (M.op X0 X0) X1
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X0 X1
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e71 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e66 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e67 X0 X1 X2
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e67 X0 X1 (M.op X1 X0)
             have r₂ := b1e15 (M.op X1 (M.op X1 X0)) (M.op X1 X0)
             grind)
          | (have r₁ := b1e67 (M.op (M.op X0 X2) X2) X0 X2
             have r₂ := b1e15 X0 (M.op (M.op X0 X2) X2)
             grind)
          | (have r₁ := b1e67 X0 X1 X2
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e67 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e71 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e71 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e71 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e106 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X2) X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e32 X1 X2 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e32 X0 X1 X2
             have i₂ := b1e17 (M.op X0 X2) X1
             grind)
          | exact superpose b1e17 b1e32
          | (have j1 := b1e17 X0 X1
             grind)
          | exact resolve b1e32 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op X0 X1) X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e32 (M.op X0 X2) X3 X2
             have i₂ := b1e32 X0 X2 X1
             grind)
          | (have i₁ := b1e32 (M.op X0 X2) X3 X2
             have i₂ := b1e32 X0 X1 X2
             grind)
          | exact superpose b1e32 b1e32
          | exact resolve b1e32 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e109 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e32 (M.op X0 X1) X2 X1
             have i₂ := b1e12 X0 X1
             grind)
          | exact superpose b1e12 b1e32
          | exact resolve b1e32 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e123 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X2) X2) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e106 X0 X1 X2
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e106 X0 X1 (M.op X0 X1)
             have r₂ := b1e15 (M.op X1 (M.op X0 X1)) (M.op X0 X1)
             grind)
          | (have r₁ := b1e106 X0 X1 X2
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e106 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106
        have b1e143 : (σ y) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e34
             grind)
          | exact superpose b1e34 b1e21
          | exact resolve b1e21 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e176 : ∀ X0 : G, (M.op (M.op y y) (M.op x x)) = (M.op (M.op (M.op y y) X0) X0) := by
          intro X0
          first
          | (have i₁ := b1e32 (M.op y y) (M.op x x) X0
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e32
          | exact resolve b1e32 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e180 : (M.op (M.op y y) (M.op x x)) = (M.op (M.op y (M.op y y)) y) := by
          first
          | (have i₁ := b1e176 x
             have i₂ := b1e109 y y x
             grind)
          | exact superpose b1e109 b1e176
          | exact resolve b1e176 b1e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e109 b1e176
        have b1e182 : (M.op y y) = (M.op (M.op y (M.op y y)) y) := by
          first
          | (have i₁ := b1e180
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e180
          | exact resolve b1e180 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e180
        have b1e184 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e78 (σ X0) (σ X1)
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e78
          | exact resolve b1e78 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e194 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e78 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e368 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X0) = X0 ∨ (M.op (M.op (M.op X0 X1) X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          grind
        clear b1e77
        have b1e398 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e368 X0 X1
             have j1 := b1e194 (M.op (M.op X0 X1) X1) X0
             grind)
          | (have r₁ := b1e368 X1 X1
             have r₂ := b1e194 (M.op (M.op X1 X1) X1) X1
             grind)
          | exact resolve b1e368 b1e194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e194 b1e368
        have b1e540 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e63 y y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e63
          | exact resolve b1e63 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e621 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b1e540
        have b1e643 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b1e621
             have r₂ := b1e43
             grind)
          | exact resolve b1e621 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e621
        have b1e659 : (k y y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e643
             grind)
          | exact superpose b1e643 b1e13
          | exact resolve b1e13 b1e643
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e643
        have b1e672 : x = (k y y) := by
          first
          | (have i₁ := b1e659
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e659
          | exact resolve b1e659 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e659
        have b1e721 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e672
             grind)
          | exact superpose b1e672 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e672
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e722 : x = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b1e721
        have b1e1140 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 X2) X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e108 X0 X2 X1 X1
             have i₂ := b1e12 X0 X1
             grind)
          | exact superpose b1e12 b1e108
          | exact resolve b1e108 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e108
        have b1e2125 : ∀ X0 : G, (M.op (M.op y y) (M.op x x)) = (M.op X0 (M.op y y)) ∨ (M.op X0 (M.op y y)) = (k X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b1e123 X0 (M.op y y) (M.op x x)
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e123
          | (have j0 := b1e123 X0 (M.op y y) x
             grind)
          | exact resolve b1e123 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2138 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b1e123 X0 y y
             have i₂ := b1e722
             grind)
          | exact superpose b1e722 b1e123
          | (have j0 := b1e123 X0 y x
             grind)
          | exact resolve b1e123 b1e722
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123 b1e722
        have b1e2320 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b1e2138 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2138
          | (have j0 := b1e2138 X0
             grind)
          | exact resolve b1e2138 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2138
        have b1e2326 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) ∨ (M.op X0 (M.op y y)) = (k X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b1e2125 X0
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e2125
          | (have j0 := b1e2125 X0
             grind)
          | exact resolve b1e2125 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e2125
        have b1e2345 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have j0 := b1e2320 y
             have j1 := b1e15 X0 y
             grind)
          | (have r₁ := b1e2320 X0
             have r₂ := b1e15 X0 y
             grind)
          | (have r₁ := b1e2320 X0
             have r₂ := b1e15 y y
             grind)
          | exact resolve b1e2320 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2320
        have b1e2347 : ∀ X0 : G, (M.op X0 (M.op y y)) = (k X0 (M.op y y)) := by
          intro X0
          first
          | (have j0 := b1e2326 X0
             have j1 := b1e15 X0 (M.op y y)
             grind)
          | (have r₁ := b1e2326 X0
             have r₂ := b1e15 X0 (M.op y y)
             grind)
          | exact resolve b1e2326 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2326
        have b1e3268 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b1e143
             have i₂ := b1e184 y x
             grind)
          | exact superpose b1e184 b1e143
          | (have j1 := b1e184 y x
             grind)
          | exact resolve b1e143 b1e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e184
        have b1e4620 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) X0) y) ∨ (M.op y y) = (k y y) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b1e398 y X0
             have i₂ := b1e2345 (M.op (M.op y X0) X0)
             grind)
          | exact superpose b1e2345 b1e398
          | (have j0 := b1e398 y x
             have j1 := b1e2345 y
             grind)
          | exact resolve b1e398 b1e2345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e398 b1e2345
        have b1e4647 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) X0) y) ∨ (M.op y y) = (k y y) := by
          intro X0
          first
          | (have j0 := b1e4620 X0
             have j1 := b1e15 y y
             grind)
          | (have r₁ := b1e4620 X0
             have r₂ := b1e15 (M.op (M.op y X0) X0) y
             grind)
          | (have r₁ := b1e4620 X0
             have r₂ := b1e15 y y
             grind)
          | exact resolve b1e4620 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4620
        have b1e4657 : y = (M.op (M.op y (M.op y y)) y) ∨ (M.op y y) = (k y y) := by
          first
          | (have i₁ := b1e4647 x
             have i₂ := b1e1140 y y x
             grind)
          | exact superpose b1e1140 b1e4647
          | exact resolve b1e4647 b1e1140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1140 b1e4647
        have b1e4661 : y = (M.op y y) ∨ (M.op y y) = (k y y) := by
          first
          | (have i₁ := b1e4657
             have i₂ := b1e182
             grind)
          | exact superpose b1e182 b1e4657
          | exact resolve b1e4657 b1e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e182 b1e4657
        have b1e4664 : (M.op y y) = (k y y) := by
          first
          | (have j1 := b1e15 y y
             grind)
          | (have r₁ := b1e4661
             have r₂ := b1e15 y y
             grind)
          | exact resolve b1e4661 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4661
        have b1e4666 : x = (M.op y y) := by
          first
          | (have i₁ := b1e4664
             have i₂ := b1e672
             grind)
          | exact superpose b1e672 b1e4664
          | exact resolve b1e4664 b1e672
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e672 b1e4664
        have b1e4868 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e2347 X0
             have i₂ := b1e4666
             grind)
          | exact superpose b1e4666 b1e2347
          | exact resolve b1e2347 b1e4666
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2347
        have b1e4882 : (M.op x y) = (M.op (M.op x y) x) := by
          first
          | (have i₁ := b1e33 y y
             have i₂ := b1e4666
             grind)
          | exact superpose b1e4666 b1e33
          | exact resolve b1e33 b1e4666
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e4666
        have b1e4911 : y = (M.op y x) := by
          first
          | (have i₁ := b1e4882
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e4882
          | exact resolve b1e4882 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4882
        have b1e35013 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e3268
             have i₂ := b1e4868 y
             grind)
          | exact superpose b1e4868 b1e3268
          | exact resolve b1e3268 b1e4868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3268 b1e4868
        have b1e35041 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e35013
             have i₂ := b1e4911
             grind)
          | exact superpose b1e4911 b1e35013
          | exact resolve b1e35013 b1e4911
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35013
        have b1e35042 : (σ x) = (σ (M.op y x)) := by grind
        clear b1e35041
        have b1e35057 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e35042
             have i₂ := b1e4911
             grind)
          | exact superpose b1e4911 b1e35042
          | exact resolve b1e35042 b1e4911
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4911 b1e35042
        have b1e36745 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e143
             have i₂ := b1e35057
             grind)
          | exact superpose b1e35057 b1e143
          | exact resolve b1e143 b1e35057
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e143
        have b1e36848 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e36745
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e36745
          | exact resolve b1e36745 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36745
        have b1e36877 : False := by grind
        exact b1e36877
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e35 : y ≠ y ∨ y = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : y = (k x y) := by grind
        clear b2e35
        have b2e62 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
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
        have b2e66 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e62 X0
             have j1 := b2e15 X0 (σ y)
             grind)
          | (have r₁ := b2e62 X0
             have r₂ := b2e15 X0 (σ y)
             grind)
          | exact resolve b2e62 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e150 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e66 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e151 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e150
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e150
          | exact resolve b2e150 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150
        have b2e152 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e151
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e151
          | exact resolve b2e151 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e151
        have b2e153 : False := by grind
        exact b2e153
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X1) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X2
             have i₂ := b3e12 X0 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op X0 X0)
             have i₂ := b3e12 X0 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e12 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b3e12 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : (σ y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e24
          | exact resolve b3e24 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e32 : y ≠ (M.op y x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e20
          | exact resolve b3e20 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e48 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e49 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e12 X0 X1
             have i₂ := b3e17 (M.op X0 X0) X1
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X1
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X1 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 (M.op X0 X1) X1
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X0 X1
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | (have r₁ := b3e15 X0 (M.op X1 X1)
             have r₂ := b3e17 (M.op X0 (M.op X1 X1)) X1
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e12 X0 X1
             have i₂ := b3e17 (M.op X0 X1) X1
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X1
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e48 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e51 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e51 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e51 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e56 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e50 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e50 (M.op X0 X1) (k X0 X1)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e50 (k X0 X1) (M.op X0 X1)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e50 (M.op X0 (k X1 X1)) X1
             have r₂ := b3e15 X0 (k X1 X1)
             grind)
          | exact resolve b3e50 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e49 X0 X1 X2
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e49 X0 X1 (M.op X1 X0)
             have r₂ := b3e15 (M.op X1 (M.op X1 X0)) (M.op X1 X0)
             grind)
          | (have r₁ := b3e49 (M.op (M.op X0 X2) X2) X0 X2
             have r₂ := b3e15 X0 (M.op (M.op X0 X2) X2)
             grind)
          | (have r₁ := b3e49 X0 X1 X2
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e49 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e52 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e52 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e52 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e99 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op X0 X1) X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e27 (M.op X0 X2) X3 X2
             have i₂ := b3e27 X0 X2 X1
             grind)
          | (have i₁ := b3e27 (M.op X0 X2) X3 X2
             have i₂ := b3e27 X0 X1 X2
             grind)
          | exact superpose b3e27 b3e27
          | exact resolve b3e27 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e101 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
          intro X0
          first
          | (have i₁ := b3e27 (σ x) X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e27
          | exact resolve b3e27 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e138 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e25 X0 X1
             have i₂ := b3e58 (τ X0) X1
             grind)
          | exact superpose b3e58 b3e25
          | (have j1 := b3e58 (τ X0) X1
             grind)
          | exact resolve b3e25 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e58
        have b3e188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X0 X1
             have i₂ := b3e55 (σ X0) (σ X1)
             grind)
          | exact superpose b3e55 b3e18
          | (have j1 := b3e55 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e196 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e28 X1 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e28 X0 X1
             have i₂ := b3e17 (M.op X0 X1) X1
             grind)
          | exact superpose b3e17 b3e28
          | (have j1 := b3e17 X0 X1
             grind)
          | exact resolve b3e28 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e198 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) (M.op (M.op X0 X2) (M.op X0 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e28 (M.op X0 X1) X1
             have i₂ := b3e27 X0 X1 X2
             grind)
          | (have i₁ := b3e28 (M.op X0 X2) X2
             have i₂ := b3e27 X0 X1 X2
             grind)
          | exact superpose b3e27 b3e28
          | exact resolve b3e28 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e199 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 (M.op X0 X0)) X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e28 (M.op X0 X1) X1
             have i₂ := b3e12 X0 X1
             grind)
          | exact superpose b3e12 b3e28
          | exact resolve b3e28 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e230 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e196 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e196 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e196 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196
        have b3e328 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (M.op (σ X1) X2) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e18 X0 X1
             have i₂ := b3e57 (σ X0) (σ X1) X2
             grind)
          | exact superpose b3e57 b3e18
          | (have j1 := b3e57 (σ X0) (σ X1) X2
             grind)
          | exact resolve b3e18 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e500 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e46 X0 X0
             have i₂ := b3e17 X0 (σ X0)
             grind)
          | (have i₁ := b3e46 X0 X1
             have i₂ := b3e17 (M.op (σ X0) (σ X1)) X1
             grind)
          | exact superpose b3e17 b3e46
          | (have j1 := b3e17 X0 (σ X1)
             grind)
          | exact resolve b3e46 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e570 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e500 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e500
        have b3e592 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e570 X0 X1
             have j1 := b3e15 X0 (σ X1)
             grind)
          | (have r₁ := b3e570 (M.op X0 (σ (k X1 X1))) X1
             have r₂ := b3e15 X0 (σ (k X1 X1))
             grind)
          | (have r₁ := b3e570 (M.op X0 (σ X1)) X1
             have r₂ := b3e15 X0 (σ X1)
             grind)
          | (have r₁ := b3e570 X0 X1
             have r₂ := b3e15 X0 (σ X1)
             grind)
          | exact resolve b3e570 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e570
        have b3e1035 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 X2) X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e99 X0 X2 X1 X1
             have i₂ := b3e12 X0 X1
             grind)
          | exact superpose b3e12 b3e99
          | exact resolve b3e99 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e1890 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e138 (σ X0) X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e138
          | exact resolve b3e138 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e138
        have b3e1926 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e1890 X0 X1
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e1890
          | (have j0 := b3e1890 X0 X1
             grind)
          | exact resolve b3e1890 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1890
        have b3e4319 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e592 X0 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e592
          | (have j0 := b3e592 X1 (τ X0)
             grind)
          | exact resolve b3e592 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e592
        have b3e4421 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e4319 X0 X1
             have i₂ := b3e26 X0 (τ X0)
             grind)
          | exact superpose b3e26 b3e4319
          | (have j0 := b3e4319 X0 X1
             grind)
          | exact resolve b3e4319 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e4319
        have b3e4431 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e4421 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e4421
          | (have j0 := b3e4421 X0 X1
             grind)
          | exact resolve b3e4421 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4421
        have b3e4438 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e4431 X0 X1
             have j1 := b3e56 X1 X0
             grind)
          | (have r₁ := b3e4431 X0 X1
             have r₂ := b3e56 (k X0 X0) X1
             grind)
          | (have r₁ := b3e4431 X0 X0
             have r₂ := b3e56 X0 (k X0 X0)
             grind)
          | (have r₁ := b3e4431 X0 X1
             have r₂ := b3e56 (M.op X1 X0) (k X1 X0)
             grind)
          | exact resolve b3e4431 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e4431
        have b3e4531 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        clear b3e4438
        have b3e4554 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e4531 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4531
        have b3e4569 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e4554 X0
             have i₂ := b3e12 X0 X0
             grind)
          | exact superpose b3e12 b3e4554
          | (have j0 := b3e4554 X0
             grind)
          | exact resolve b3e4554 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4554
        have b3e5938 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1
             have i₂ := b3e4569 X0
             grind)
          | exact superpose b3e4569 b3e12
          | (have j1 := b3e4569 X0
             grind)
          | exact resolve b3e12 b3e4569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4569
        have b3e7760 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 (σ X0) (σ X1)
             have i₂ := b3e188 X0 X1
             grind)
          | (have i₁ := b3e15 (σ X1) (σ X0)
             have i₂ := b3e188 X0 X1
             grind)
          | exact superpose b3e188 b3e15
          | (have j1 := b3e188 X1 X0
             grind)
          | exact resolve b3e15 b3e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e7835 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e188 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e188
        have b3e7853 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e7760 X0 X1
             have i₂ := b3e18 X1 X0
             grind)
          | exact superpose b3e18 b3e7760
          | (have j0 := b3e7760 X0 X1
             grind)
          | exact resolve b3e7760 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7760
        have b3e7862 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e7853 X0 X1
             have j1 := b3e7835 X1 X0
             grind)
          | (have r₁ := b3e7853 X1 X0
             have r₂ := b3e7835 X0 X1
             grind)
          | (have r₁ := b3e7853 X1 X1
             have r₂ := b3e7835 X1 X1
             grind)
          | exact resolve b3e7853 b3e7835
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7835 b3e7853
        have b3e10905 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e230 X0 X0
             have i₂ := b3e5938 X0 X0
             grind)
          | exact superpose b3e5938 b3e230
          | (have j0 := b3e230 X0 X0
             have j1 := b3e5938 X0 x
             grind)
          | exact resolve b3e230 b3e5938
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e230 b3e5938
        have b3e11015 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e10905 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10905
        have b3e11043 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e11015 X0
             have j1 := b3e15 X0 X0
             grind)
          | (have r₁ := b3e11015 x
             have r₂ := b3e15 x x
             grind)
          | exact resolve b3e11015 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11015
        have b3e11221 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e11043 (σ X0)
             grind)
          | exact superpose b3e11043 b3e18
          | exact resolve b3e18 b3e11043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e11241 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e11221 X0
             have i₂ := b3e11043 X0
             grind)
          | exact superpose b3e11043 b3e11221
          | exact resolve b3e11221 b3e11043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11043 b3e11221
        have b3e12042 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) X0) X0) (σ X1)) ∨ (M.op (σ X1) (σ x)) = (σ (k X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e101 (σ X1)
             have i₂ := b3e328 X1 x X0
             grind)
          | exact superpose b3e328 b3e101
          | (have j1 := b3e328 X1 x x
             grind)
          | exact resolve b3e101 b3e328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e328
        have b3e12234 : ∀ X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ X1)) ∨ (M.op (σ X1) (σ x)) = (σ (k X1 x)) := by
          intro X1
          first
          | (have i₁ := b3e12042 x X1
             have i₂ := b3e101 x
             grind)
          | exact superpose b3e101 b3e12042
          | (have j0 := b3e12042 x X1
             grind)
          | exact resolve b3e12042 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12042
        have b3e12323 : ∀ X1 : G, (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ X1)) ∨ (M.op (σ X1) (σ x)) = (σ (k X1 x)) := by
          intro X1
          first
          | (have i₁ := b3e12234 X1
             have i₂ := b3e11241 y
             grind)
          | exact superpose b3e11241 b3e12234
          | (have j0 := b3e12234 X1
             grind)
          | exact resolve b3e12234 b3e11241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12234
        have b3e12362 : ∀ X1 : G, (σ x) = (M.op (σ x) (σ X1)) ∨ (M.op (σ X1) (σ x)) = (σ (k X1 x)) := by
          intro X1
          first
          | (have i₁ := b3e12323 X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12323
          | (have j0 := b3e12323 X1
             grind)
          | exact resolve b3e12323 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12323
        have b3e12370 : ∀ X1 : G, (M.op (σ X1) (σ x)) = (σ (k X1 x)) := by
          intro X1
          first
          | (have j0 := b3e12362 X1
             have j1 := b3e7862 x X1
             grind)
          | (have r₁ := b3e12362 X1
             have r₂ := b3e7862 x X1
             grind)
          | exact resolve b3e12362 b3e7862
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7862 b3e12362
        have b3e12429 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ (k X0 x)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ X0) (σ x)
             have i₂ := b3e12370 X0
             grind)
          | exact superpose b3e12370 b3e12
          | exact resolve b3e12 b3e12370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e12487 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (k (k X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b3e12429 X0
             have i₂ := b3e12370 (k X0 x)
             grind)
          | exact superpose b3e12370 b3e12429
          | exact resolve b3e12429 b3e12370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12429
        have b3e12527 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (k X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b3e12487 X0
             have i₂ := b3e11241 X0
             grind)
          | exact superpose b3e11241 b3e12487
          | exact resolve b3e12487 b3e11241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12487
        have b3e14089 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) X0) (σ y)) (M.op (σ y) (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e198 (σ x) x (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e198
          | exact resolve b3e198 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e198
        have b3e14225 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) X0) (σ y)) (σ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b3e14089 X0
             have i₂ := b3e11241 y
             grind)
          | exact superpose b3e11241 b3e14089
          | exact resolve b3e14089 b3e11241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14089
        have b3e14287 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) X0) (σ y)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e14225 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e14225
          | exact resolve b3e14225 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14225
        have b3e14317 : (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) := by
          first
          | (have i₁ := b3e14287 x
             have i₂ := b3e101 x
             grind)
          | exact superpose b3e101 b3e14287
          | exact resolve b3e14287 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101 b3e14287
        have b3e14340 : (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ x)) := by
          first
          | (have i₁ := b3e14317
             have i₂ := b3e1035 (σ y) (σ x) (σ y)
             grind)
          | exact superpose b3e1035 b3e14317
          | exact resolve b3e14317 b3e1035
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14317
        have b3e14357 : (M.op (σ (M.op y y)) (σ y)) = (M.op (M.op (σ y) (σ (M.op y y))) (σ x)) := by
          first
          | (have i₁ := b3e14340
             have i₂ := b3e11241 y
             grind)
          | exact superpose b3e11241 b3e14340
          | exact resolve b3e14340 b3e11241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14340
        have b3e14368 : (M.op (σ (M.op y y)) (σ y)) = (M.op (σ (k (k y x) x)) (σ x)) := by
          first
          | (have i₁ := b3e14357
             have i₂ := b3e12527 y
             grind)
          | exact superpose b3e12527 b3e14357
          | exact resolve b3e14357 b3e12527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14357
        have b3e14375 : (M.op (σ (M.op y y)) (σ y)) = (σ (k (k (k y x) x) x)) := by
          first
          | (have i₁ := b3e14368
             have i₂ := b3e12370 (k (k y x) x)
             grind)
          | exact superpose b3e12370 b3e14368
          | exact resolve b3e14368 b3e12370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14368
        have b3e14380 : (M.op (σ x) (σ y)) = (σ (k (k (k y x) x) x)) := by
          first
          | (have i₁ := b3e14375
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e14375
          | exact resolve b3e14375 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14375
        have b3e14384 : (σ y) = (σ (k (k (k y x) x) x)) := by
          first
          | (have i₁ := b3e14380
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e14380
          | exact resolve b3e14380 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14380
        have b3e14462 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ X0) (σ X0)
             have i₂ := b3e11241 X0
             grind)
          | exact superpose b3e11241 b3e12
          | exact resolve b3e12 b3e11241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e14536 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (k X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b3e14462 X0
             have i₂ := b3e12527 X0
             grind)
          | exact superpose b3e12527 b3e14462
          | exact resolve b3e14462 b3e12527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14462
        have b3e14743 : (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b3e199 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e199
          | exact resolve b3e199 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e199
        have b3e14903 : (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b3e14743
             have i₂ := b3e11241 y
             grind)
          | exact superpose b3e11241 b3e14743
          | exact resolve b3e14743 b3e11241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14743
        have b3e14998 : (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) (σ x)) := by
          first
          | (have i₁ := b3e14903
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e14903
          | exact resolve b3e14903 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14903
        have b3e15051 : (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) := by
          first
          | (have i₁ := b3e14998
             have i₂ := b3e29
             grind)
          | exact superpose b3e29 b3e14998
          | exact resolve b3e14998 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e14998
        have b3e15085 : (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ x)) := by
          first
          | (have i₁ := b3e15051
             have i₂ := b3e1035 (σ y) (σ x) (σ y)
             grind)
          | exact superpose b3e1035 b3e15051
          | exact resolve b3e15051 b3e1035
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1035 b3e15051
        have b3e15097 : (M.op (σ (M.op y y)) (σ y)) = (M.op (M.op (σ y) (σ (M.op y y))) (σ x)) := by
          first
          | (have i₁ := b3e15085
             have i₂ := b3e11241 y
             grind)
          | exact superpose b3e11241 b3e15085
          | exact resolve b3e15085 b3e11241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11241 b3e15085
        have b3e15106 : (M.op (σ (M.op y y)) (σ y)) = (M.op (σ (k (k y x) x)) (σ x)) := by
          first
          | (have i₁ := b3e15097
             have i₂ := b3e12527 y
             grind)
          | exact superpose b3e12527 b3e15097
          | exact resolve b3e15097 b3e12527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12527 b3e15097
        have b3e15113 : (M.op (σ (M.op y y)) (σ y)) = (σ (k (k (k y x) x) x)) := by
          first
          | (have i₁ := b3e15106
             have i₂ := b3e12370 (k (k y x) x)
             grind)
          | exact superpose b3e12370 b3e15106
          | exact resolve b3e15106 b3e12370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15106
        have b3e15119 : (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
          first
          | (have i₁ := b3e15113
             have i₂ := b3e14384
             grind)
          | exact superpose b3e14384 b3e15113
          | exact resolve b3e15113 b3e14384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15113
        have b3e15122 : (σ y) = (σ (k (k y x) x)) := by
          first
          | (have i₁ := b3e15119
             have i₂ := b3e14536 y
             grind)
          | exact superpose b3e14536 b3e15119
          | exact resolve b3e15119 b3e14536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14536 b3e15119
        have b3e15187 : (M.op (σ y) (σ x)) = (σ (k (k (k y x) x) x)) := by
          first
          | (have i₁ := b3e12370 (k (k y x) x)
             have i₂ := b3e15122
             grind)
          | exact superpose b3e15122 b3e12370
          | exact resolve b3e12370 b3e15122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15122
        have b3e15188 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e15187
             have i₂ := b3e14384
             grind)
          | exact superpose b3e14384 b3e15187
          | exact resolve b3e15187 b3e14384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14384 b3e15187
        have b3e15221 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e15188
             have i₂ := b3e12370 y
             grind)
          | exact superpose b3e12370 b3e15188
          | exact resolve b3e15188 b3e12370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12370 b3e15188
        have b3e15884 : (σ y) = (σ (M.op y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b3e1926 y x
             have i₂ := b3e15221
             grind)
          | exact superpose b3e15221 b3e1926
          | (have j0 := b3e1926 y x
             grind)
          | exact resolve b3e1926 b3e15221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1926
        have b3e15885 : (τ (σ y)) = (k y x) := by
          first
          | (have i₁ := b3e13 (k y x)
             have i₂ := b3e15221
             grind)
          | exact superpose b3e15221 b3e13
          | exact resolve b3e13 b3e15221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15221
        have b3e15939 : y = (k y x) := by
          first
          | (have i₁ := b3e15885
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e15885
          | exact resolve b3e15885 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15885
        have b3e15940 : x = (k y x) := by
          first
          | (have r₁ := b3e15884
             have r₂ := b3e31
             grind)
          | exact resolve b3e15884 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e15884
        have b3e15957 : x = y := by
          first
          | (have i₁ := b3e15940
             have i₂ := b3e15939
             grind)
          | exact superpose b3e15939 b3e15940
          | exact resolve b3e15940 b3e15939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15939 b3e15940
        have b3e16161 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e15957
             grind)
          | exact superpose b3e15957 b3e32
          | exact resolve b3e32 b3e15957
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e16218 : x ≠ y := by
          first
          | (have i₁ := b3e16161
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16161
          | exact resolve b3e16161 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e16161
        have b3e16241 : False := by grind
        exact b3e16241
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x y) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
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
          have b4e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e14
            | exact resolve b4e14 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X2
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X0 X0)
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e13 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e13 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : y ≠ (M.op y x) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e21
            | exact resolve b4e21 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : (M.op x (M.op x x)) = (M.op (M.op y x) y) := by
            first
            | (have i₁ := b4e13 x y
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op (M.op X0 X1) X1) = (k X0 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 (M.op X0 X0)
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e16
            | (have r₁ := b4e16 (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))
               have r₂ := b4e13 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b4e41
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e41
            | exact resolve b4e41 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e52 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e18 X2 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e18 X0 X1
               have i₂ := b4e18 (M.op X1 X1) X1
               grind)
            | exact superpose b4e18 b4e18
            | (have j0 := b4e18 X2 X1
               have j1 := b4e18 X2 X1
               grind)
            | exact resolve b4e18 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e59 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 (M.op X0 X1) X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e16 X0 (M.op X1 X1)
               have r₂ := b4e18 (M.op X0 (M.op X1 X1)) X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e13 X0 X1
               have i₂ := b4e18 (M.op X0 X1) X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 X1
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e60 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e60 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e60 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e67 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e59 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e59 (M.op X0 X1) (k X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e59 (k X0 X1) (M.op X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e59 (M.op X0 (k X1 X1)) X1
               have r₂ := b4e16 X0 (k X1 X1)
               grind)
            | exact resolve b4e59 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e71 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e52 X0 X1 X2
               have j1 := b4e16 X2 X1
               grind)
            | (have r₁ := b4e52 (M.op X0 X1) X1 X1
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e52 X1 X1 (M.op X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e52 X0 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e52 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e72 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e71 X0 X1 X2
               have j1 := b4e16 X2 X1
               grind)
            | (have r₁ := b4e71 (M.op X0 X1) X1 X1
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e71 X1 X1 (M.op X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e71 X0 X1 X2
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e71 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e27 X1 X0
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e85 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e31
            | exact resolve b4e31 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e109 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X2) X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 X1 X2 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e33 X0 X1 X2
               have i₂ := b4e18 (M.op X0 X2) X1
               grind)
            | exact superpose b4e18 b4e33
            | (have j1 := b4e18 X0 X1
               grind)
            | exact resolve b4e33 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e112 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 (M.op X0 X1) X2 X1
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e33
            | exact resolve b4e33 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e126 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X2) X2) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e109 X0 X1 X2
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e109 X0 X1 (M.op X0 X1)
               have r₂ := b4e16 (M.op X1 (M.op X0 X1)) (M.op X0 X1)
               grind)
            | (have r₁ := b4e109 X0 X1 X2
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e109 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e146 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e35
               grind)
            | exact superpose b4e35 b4e20
            | exact resolve b4e20 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e153 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e146
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e146
            | exact resolve b4e146 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e146
          have b4e223 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e66 (σ X0) (σ X1)
               grind)
            | exact superpose b4e66 b4e19
            | (have j1 := b4e66 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e232 : ∀ X0 : G, (M.op (M.op (M.op y x) X0) X0) = (M.op (M.op x (M.op x x)) y) := by
            intro X0
            first
            | (have i₁ := b4e33 (M.op y x) y X0
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e33
            | exact resolve b4e33 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e234 : (M.op (M.op x (M.op x x)) y) = (M.op (M.op y (M.op y y)) x) := by
            first
            | (have i₁ := b4e232 x
               have i₂ := b4e112 y x x
               grind)
            | exact superpose b4e112 b4e232
            | exact resolve b4e232 b4e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112 b4e232
          have b4e236 : (M.op (M.op x (M.op x x)) y) = (M.op (M.op y x) x) := by
            first
            | (have i₁ := b4e234
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e234
            | exact resolve b4e234 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e234
          have b4e238 : (M.op y (M.op y y)) = (M.op (M.op x (M.op x x)) y) := by
            first
            | (have i₁ := b4e236
               have i₂ := b4e13 y x
               grind)
            | exact superpose b4e13 b4e236
            | exact resolve b4e236 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e236
          have b4e240 : (M.op y x) = (M.op (M.op x (M.op x x)) y) := by
            first
            | (have i₁ := b4e238
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e238
            | exact resolve b4e238 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e238
          have b4e243 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e34 X0 X1
               have i₂ := b4e18 (M.op X0 X1) X1
               grind)
            | exact superpose b4e18 b4e34
            | (have j1 := b4e18 X0 X1
               grind)
            | exact resolve b4e34 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e249 : (M.op (M.op x (M.op x x)) y) = (M.op (M.op (M.op x (M.op x x)) y) (M.op (M.op y x) (M.op y x))) := by
            first
            | (have i₁ := b4e34 (M.op y x) y
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e34
            | exact resolve b4e34 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e268 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X0)) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 (M.op (M.op X0 X1) X1) (M.op X0 X0) X2
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e33
            | exact resolve b4e33 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e272 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e268 X0 X1 X2
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e268
            | exact resolve b4e268 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e268
          have b4e283 : (M.op y x) = (M.op (M.op y x) (M.op (M.op y x) (M.op y x))) := by
            first
            | (have i₁ := b4e249
               have i₂ := b4e240
               grind)
            | exact superpose b4e240 b4e249
            | exact resolve b4e249 b4e240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e249
          have b4e285 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e243 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e243 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e243 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e243
          have b4e422 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = X2 ∨ (M.op X2 (σ X1)) = (k X2 (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e72 (σ X0) (σ X1) X2
               grind)
            | exact superpose b4e72 b4e19
            | (have j1 := b4e72 (σ X0) (σ X1) X2
               grind)
            | exact resolve b4e19 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e466 : (M.op (M.op x (M.op x x)) y) ≠ (M.op (M.op y x) (M.op y x)) ∨ (M.op (M.op x (M.op x x)) y) = (k (M.op y x) (M.op (M.op y x) (M.op y x))) := by
            first
            | (have i₁ := b4e39 (M.op y x) y
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e39
            | exact resolve b4e39 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e484 : (M.op y x) ≠ (M.op (M.op y x) (M.op y x)) ∨ (M.op (M.op x (M.op x x)) y) = (k (M.op y x) (M.op (M.op y x) (M.op y x))) := by
            first
            | (have i₁ := b4e466
               have i₂ := b4e240
               grind)
            | exact superpose b4e240 b4e466
            | exact resolve b4e466 b4e240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e466
          have b4e495 : (M.op y x) ≠ (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (k (M.op y x) (M.op (M.op y x) (M.op y x))) := by
            first
            | (have i₁ := b4e484
               have i₂ := b4e240
               grind)
            | exact superpose b4e240 b4e484
            | exact resolve b4e484 b4e240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e484
          have b4e530 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e54 y y
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e54
            | exact resolve b4e54 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e533 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e54 X0 X0
               have i₂ := b4e18 X0 (σ X0)
               grind)
            | (have i₁ := b4e54 X0 X1
               have i₂ := b4e18 (M.op (σ X0) (σ X1)) X1
               grind)
            | exact superpose b4e18 b4e54
            | (have j1 := b4e18 X0 (σ X1)
               grind)
            | exact resolve b4e54 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e568 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 X1
               have i₂ := b4e54 X1 X0
               grind)
            | exact superpose b4e54 b4e14
            | (have j1 := b4e54 X1 X0
               grind)
            | exact resolve b4e14 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e605 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e533 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533
          have b4e607 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b4e530
          have b4e628 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e605 X0 X1
               have j1 := b4e16 X0 (σ X1)
               grind)
            | (have r₁ := b4e605 (M.op X0 (σ (k X1 X1))) X1
               have r₂ := b4e16 X0 (σ (k X1 X1))
               grind)
            | (have r₁ := b4e605 (M.op X0 (σ X1)) X1
               have r₂ := b4e16 X0 (σ X1)
               grind)
            | (have r₁ := b4e605 X0 X1
               have r₂ := b4e16 X0 (σ X1)
               grind)
            | exact resolve b4e605 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e605
          have b4e629 : (σ x) = (σ (k y y)) := by
            first
            | (have r₁ := b4e607
               have r₂ := b4e44
               grind)
            | exact resolve b4e607 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e607
          have b4e647 : (k y y) = (τ (σ x)) := by
            first
            | (have i₁ := b4e14 (k y y)
               have i₂ := b4e629
               grind)
            | exact superpose b4e629 b4e14
            | exact resolve b4e14 b4e629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e649 : ∀ X0 : G, (σ (k X0 (k y y))) = (k (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 (k y y)
               have i₂ := b4e629
               grind)
            | exact superpose b4e629 b4e19
            | exact resolve b4e19 b4e629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e629
          have b4e658 : ∀ X0 : G, (σ (k X0 (k y y))) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e649 X0
               have i₂ := b4e19 X0 x
               grind)
            | exact superpose b4e19 b4e649
            | exact resolve b4e649 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e649
          have b4e660 : x = (k y y) := by
            first
            | (have i₁ := b4e647
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e647
            | exact resolve b4e647 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e647
          have b4e2020 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X0 (M.op (M.op X1 X2) X2)) ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = (k X0 (M.op (M.op X1 X2) X2)) ∨ (M.op (M.op X1 X2) X2) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e272 X1 X2 (M.op (M.op X1 X2) X2)
               have i₂ := b4e18 X0 (M.op (M.op X1 X2) X2)
               grind)
            | (have i₁ := b4e272 X0 X1 X2
               have i₂ := b4e18 (M.op (M.op (M.op X0 X1) X1) X2) X1
               grind)
            | exact superpose b4e18 b4e272
            | (have j1 := b4e18 X0 (M.op (M.op X1 X2) X2)
               grind)
            | exact resolve b4e272 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272
          have b4e2062 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X0 (M.op (M.op X1 X2) X2)) ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = (k X0 (M.op (M.op X1 X2) X2)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e2020 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2020
          have b4e2075 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (k X0 (M.op (M.op X1 X2) X2)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e2062 X0 X1 X2
               have j1 := b4e16 X0 (M.op (M.op X1 X2) X2)
               grind)
            | (have r₁ := b4e2062 X0 X1 X2
               have r₂ := b4e16 X0 (M.op (M.op X1 X2) X2)
               grind)
            | exact resolve b4e2062 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2062
          have b4e2197 : ∀ X0 : G, (M.op (M.op x (M.op x x)) y) = (M.op X0 (M.op y x)) ∨ (M.op X0 (M.op y x)) = (k X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b4e126 X0 (M.op y x) y
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e126
            | (have j0 := b4e126 X0 (M.op y x) x
               grind)
            | exact resolve b4e126 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e126
          have b4e2392 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) ∨ (M.op X0 (M.op y x)) = (k X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b4e2197 X0
               have i₂ := b4e240
               grind)
            | exact superpose b4e240 b4e2197
            | (have j0 := b4e2197 X0
               grind)
            | exact resolve b4e2197 b4e240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e240 b4e2197
          have b4e2414 : ∀ X0 : G, (M.op X0 (M.op y x)) = (k X0 (M.op y x)) := by
            intro X0
            first
            | (have j0 := b4e2392 X0
               have j1 := b4e16 X0 (M.op y x)
               grind)
            | (have r₁ := b4e2392 X0
               have r₂ := b4e16 X0 (M.op y x)
               grind)
            | exact resolve b4e2392 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2392
          have b4e5888 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e628 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e628
            | (have j0 := b4e628 X1 (τ X0)
               grind)
            | exact resolve b4e628 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e628
          have b4e6019 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e5888 X0 X1
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e5888
            | (have j0 := b4e5888 X0 X1
               grind)
            | exact resolve b4e5888 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5888
          have b4e6037 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e6019 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e6019
            | (have j0 := b4e6019 X0 X1
               grind)
            | exact resolve b4e6019 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6019
          have b4e6049 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e6037 X0 X1
               have j1 := b4e67 X1 X0
               grind)
            | (have r₁ := b4e6037 X0 X1
               have r₂ := b4e67 (k X0 X0) X1
               grind)
            | (have r₁ := b4e6037 X0 X0
               have r₂ := b4e67 X0 (k X0 X0)
               grind)
            | (have r₁ := b4e6037 X0 X1
               have r₂ := b4e67 (M.op X1 X0) (k X1 X0)
               grind)
            | exact resolve b4e6037 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e6037
          have b4e6158 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            grind
          have b4e6170 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X0 X1
               have i₂ := b4e6049 X1 (τ X0)
               grind)
            | exact superpose b4e6049 b4e26
            | (have j1 := b4e6049 X1 (τ X0)
               grind)
            | exact resolve b4e26 b4e6049
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6186 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e6158 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6158
          have b4e6201 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e6186 X0
               have i₂ := b4e13 X0 X0
               grind)
            | exact superpose b4e13 b4e6186
            | (have j0 := b4e6186 X0
               grind)
            | exact resolve b4e6186 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6186
          have b4e6979 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1
               have i₂ := b4e6201 X0
               grind)
            | exact superpose b4e6201 b4e13
            | (have j1 := b4e6201 X0
               grind)
            | exact resolve b4e13 b4e6201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6201
          have b4e9973 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) (σ X1)
               have i₂ := b4e223 X0 X1
               grind)
            | (have i₁ := b4e16 (σ X1) (σ X0)
               have i₂ := b4e223 X0 X1
               grind)
            | exact superpose b4e223 b4e16
            | (have j1 := b4e223 X1 X0
               grind)
            | exact resolve b4e16 b4e223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e10053 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e223 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e10074 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e9973 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e9973
            | (have j0 := b4e9973 X0 X1
               grind)
            | exact resolve b4e9973 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9973
          have b4e10093 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e10074 X0 X1
               have j1 := b4e10053 X1 X0
               grind)
            | (have r₁ := b4e10074 X1 X0
               have r₂ := b4e10053 X0 X1
               grind)
            | (have r₁ := b4e10074 X1 X1
               have r₂ := b4e10053 X1 X1
               grind)
            | exact resolve b4e10074 b4e10053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10074
          have b4e13265 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e285 X0 X0
               have i₂ := b4e6979 X0 X0
               grind)
            | exact superpose b4e6979 b4e285
            | (have j0 := b4e285 X0 X0
               have j1 := b4e6979 X0 x
               grind)
            | exact resolve b4e285 b4e6979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6979
          have b4e13381 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e13265 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13265
          have b4e13412 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e13381 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e13381 x
               have r₂ := b4e16 x x
               grind)
            | exact resolve b4e13381 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13381
          have b4e13730 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e6049 X0 X1
               have i₂ := b4e13412 X0
               grind)
            | exact superpose b4e13412 b4e6049
            | (have j0 := b4e6049 X0 X1
               grind)
            | exact resolve b4e6049 b4e13412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6049
          have b4e13739 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e13412 (σ X0)
               grind)
            | exact superpose b4e13412 b4e19
            | exact resolve b4e19 b4e13412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e13743 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e85 X0 X0
               have i₂ := b4e13412 (τ X0)
               grind)
            | exact superpose b4e13412 b4e85
            | exact resolve b4e85 b4e13412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85
          have b4e13756 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13743 X0
               have i₂ := b4e13412 X0
               grind)
            | exact superpose b4e13412 b4e13743
            | exact resolve b4e13743 b4e13412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13743
          have b4e13760 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13739 X0
               have i₂ := b4e13412 X0
               grind)
            | exact superpose b4e13412 b4e13739
            | exact resolve b4e13739 b4e13412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13739
          have b4e15629 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 (k y y))) ∨ (M.op (k y y) (k y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e658 X0
               have i₂ := b4e13730 (k y y) X0
               grind)
            | exact superpose b4e13730 b4e658
            | (have j1 := b4e13730 (k y y) X0
               grind)
            | exact resolve b4e658 b4e13730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13730
          have b4e15683 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op (k y y) (k y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e15629 X0
               have i₂ := b4e660
               grind)
            | exact superpose b4e660 b4e15629
            | (have j0 := b4e15629 X0
               grind)
            | exact resolve b4e15629 b4e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15629
          have b4e15714 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op x x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e15683 X0
               have i₂ := b4e660
               grind)
            | exact superpose b4e660 b4e15683
            | (have j0 := b4e15683 X0
               grind)
            | exact resolve b4e15683 b4e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15683
          have b4e20585 : ∀ X0 X1 X2 : G, (τ X0) = X1 ∨ (σ (k X1 X2)) = (M.op (σ X1) (σ X2)) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e14 X1
               have i₂ := b4e422 X1 X2 X0
               grind)
            | (have i₁ := b4e14 X0
               have i₂ := b4e422 X0 X1 (σ X0)
               grind)
            | exact superpose b4e422 b4e14
            | (have j1 := b4e422 X1 X2 X0
               grind)
            | exact resolve b4e14 b4e422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e422
          have b4e32400 : (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (k (M.op y x) (M.op (M.op y x) (M.op y x))) := by
            first
            | (have i₁ := b4e285 (M.op y x) (M.op (M.op y x) (M.op y x))
               have i₂ := b4e283
               grind)
            | exact superpose b4e283 b4e285
            | exact resolve b4e285 b4e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e283 b4e285
          have b4e32447 : (M.op y x) = (k (M.op y x) (M.op (M.op y x) (M.op y x))) := by
            first
            | (have r₁ := b4e32400
               have r₂ := b4e495
               grind)
            | exact resolve b4e32400 b4e495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e495 b4e32400
          have b4e39049 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ X0) = (τ (M.op (σ X1) (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e568 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e568
            | (have j0 := b4e568 X1 (τ X0)
               grind)
            | exact resolve b4e568 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39117 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e568 X1 X0
               have i₂ := b4e223 X0 X1
               grind)
            | (have i₁ := b4e568 X0 X1
               have i₂ := b4e223 X0 X1
               grind)
            | exact superpose b4e223 b4e568
            | (have j0 := b4e568 X0 X1
               have j1 := b4e223 X1 X0
               grind)
            | exact resolve b4e568 b4e223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223
          have b4e39154 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e568 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e568
            | exact resolve b4e568 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e568
          have b4e39462 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 ∨ (M.op (σ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e39154 X0 X1
               have i₂ := b4e27 X0 X1
               grind)
            | exact superpose b4e27 b4e39154
            | (have j0 := b4e39154 X0 X1
               grind)
            | exact resolve b4e39154 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e39154
          have b4e39492 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e39117 X0 X1
               have j1 := b4e10053 X1 X0
               grind)
            | (have r₁ := b4e39117 X1 X0
               have r₂ := b4e10053 X0 X1
               grind)
            | (have r₁ := b4e39117 X1 X1
               have r₂ := b4e10053 X1 X1
               grind)
            | exact resolve b4e39117 b4e10053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10053 b4e39117
          have b4e39559 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ X0) = (τ (M.op (σ X1) (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39049 X0 X1
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e39049
            | (have j0 := b4e39049 X0 X1
               grind)
            | exact resolve b4e39049 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e39049
          have b4e39700 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e39462 X0 X1
               have j1 := b4e16 (σ X1) X0
               grind)
            | (have r₁ := b4e39462 X0 (M.op X0 (τ (M.op X0 X0)))
               have r₂ := b4e16 X0 (τ (M.op X0 X0))
               grind)
            | (have r₁ := b4e39462 X1 X1
               have r₂ := b4e16 (σ X1) X1
               grind)
            | exact resolve b4e39462 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39462
          have b4e39718 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e39492 X0 X1
               have j1 := b4e10093 X0 X1
               grind)
            | (have r₁ := b4e39492 X0 X1
               have r₂ := b4e10093 X0 X1
               grind)
            | exact resolve b4e39492 b4e10093
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10093 b4e39492
          have b4e39764 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ X0) = (τ (M.op (σ X1) (σ X1))) := by
            intro X0 X1
            first
            | (have j0 := b4e39559 X0 X1
               have j1 := b4e16 X0 (σ X1)
               grind)
            | (have r₁ := b4e39559 X0 X1
               have r₂ := b4e16 X0 (σ X1)
               grind)
            | exact resolve b4e39559 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39559
          have b4e39853 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39718 X0 X1
               have i₂ := b4e13760 X0
               grind)
            | exact superpose b4e13760 b4e39718
            | (have j0 := b4e39718 X0 X1
               grind)
            | exact resolve b4e39718 b4e13760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39718
          have b4e39872 : ∀ X0 X1 : G, (τ X0) = (τ (σ (M.op X1 X1))) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39764 X0 X1
               have i₂ := b4e13760 X1
               grind)
            | exact superpose b4e13760 b4e39764
            | (have j0 := b4e39764 X0 X1
               grind)
            | exact resolve b4e39764 b4e13760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13760 b4e39764
          have b4e39897 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39853 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e39853
            | (have j0 := b4e39853 X0 X1
               grind)
            | exact resolve b4e39853 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39853
          have b4e39910 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39872 X0 X1
               have i₂ := b4e14 (M.op X1 X1)
               grind)
            | exact superpose b4e14 b4e39872
            | (have j0 := b4e39872 X0 X1
               grind)
            | exact resolve b4e39872 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39872
          have b4e45315 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 X2) X2))) = (τ (M.op (σ X0) (M.op (M.op X1 X2) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e80 X0 (M.op (M.op X1 X2) X2)
               have i₂ := b4e2075 (σ X0) X1 X2
               grind)
            | exact superpose b4e2075 b4e80
            | exact resolve b4e80 b4e2075
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80 b4e2075
          have b4e49883 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39700 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e39700
            | (have j0 := b4e39700 X1 (τ X0)
               grind)
            | exact resolve b4e39700 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39700
          have b4e57604 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 (k y y))) ∨ (τ X0) = (τ (M.op (k y y) (k y y))) := by
            intro X0
            first
            | (have i₁ := b4e658 X0
               have i₂ := b4e49883 X0 (k y y)
               grind)
            | exact superpose b4e49883 b4e658
            | (have j1 := b4e49883 X0 (k y y)
               grind)
            | exact resolve b4e658 b4e49883
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e658 b4e49883
          have b4e57798 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (τ X0) = (τ (M.op (k y y) (k y y))) := by
            intro X0
            first
            | (have i₁ := b4e57604 X0
               have i₂ := b4e660
               grind)
            | exact superpose b4e660 b4e57604
            | (have j0 := b4e57604 X0
               grind)
            | exact resolve b4e57604 b4e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57604
          have b4e57868 : ∀ X0 : G, (τ X0) = (τ (M.op x x)) ∨ (σ (k X0 x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e57798 X0
               have i₂ := b4e660
               grind)
            | exact superpose b4e660 b4e57798
            | (have j0 := b4e57798 X0
               grind)
            | exact resolve b4e57798 b4e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e660 b4e57798
          have b4e64941 : (σ (M.op y x)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b4e153
               have i₂ := b4e39897 x y
               grind)
            | exact superpose b4e39897 b4e153
            | (have j1 := b4e39897 x y
               grind)
            | exact resolve b4e153 b4e39897
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39897
          have b4e65196 : y = (M.op x x) := by
            first
            | (have j1 := b4e15714 y
               grind)
            | (have r₁ := b4e64941
               have r₂ := b4e15714 y
               grind)
            | exact resolve b4e64941 b4e15714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15714 b4e64941
          have b4e177101 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e6170 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e6170
            | exact resolve b4e6170 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6170
          have b4e177223 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e177101 X0 X1
               have i₂ := b4e13412 X1
               grind)
            | exact superpose b4e13412 b4e177101
            | (have j0 := b4e177101 X0 X1
               grind)
            | exact resolve b4e177101 b4e13412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13412 b4e177101
          have b4e177256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e177223 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e177223
            | (have j0 := b4e177223 X0 X1
               grind)
            | exact resolve b4e177223 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e177223
          have b4e177489 : ∀ X0 X1 X2 : G, (τ X1) = X0 ∨ (k X1 (σ X2)) = (M.op X1 (σ X2)) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e39910 X1 X2
               have i₂ := b4e177256 X0 X2
               grind)
            | (have i₁ := b4e39910 X0 X1
               have i₂ := b4e177256 (M.op X1 X1) X1
               grind)
            | exact superpose b4e177256 b4e39910
            | (have j0 := b4e39910 X1 X2
               have j1 := b4e177256 X0 X2
               grind)
            | exact resolve b4e39910 b4e177256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39910 b4e177256
          have b4e182026 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op (M.op x x) (M.op x x))) ∨ (σ (k X0 x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e13756 X0
               have i₂ := b4e57868 X0
               grind)
            | (have i₁ := b4e13756 (M.op x x)
               have i₂ := b4e57868 X0
               grind)
            | exact superpose b4e57868 b4e13756
            | (have j1 := b4e57868 X0
               grind)
            | exact resolve b4e13756 b4e57868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57868
          have b4e182047 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op y y)) ∨ (σ (k X0 x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e182026 X0
               have i₂ := b4e65196
               grind)
            | exact superpose b4e65196 b4e182026
            | (have j0 := b4e182026 X0
               grind)
            | exact resolve b4e182026 b4e65196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65196 b4e182026
          have b4e182073 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ x) ∨ (σ (k X0 x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e182047 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e182047
            | (have j0 := b4e182047 X0
               grind)
            | exact resolve b4e182047 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e182047
          have b4e182088 : ∀ X0 : G, (τ x) = (τ (M.op X0 X0)) ∨ (σ (k X0 x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e182073 X0
               have i₂ := b4e13756 X0
               grind)
            | exact superpose b4e13756 b4e182073
            | (have j0 := b4e182073 X0
               grind)
            | exact resolve b4e182073 b4e13756
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13756 b4e182073
          have b4e201257 : ∀ X0 : G, (M.op X0 X0) = (σ (τ x)) ∨ (σ (k X0 x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op X0 X0)
               have i₂ := b4e182088 X0
               grind)
            | exact superpose b4e182088 b4e15
            | (have j1 := b4e182088 X0
               grind)
            | exact resolve b4e15 b4e182088
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e182088
          have b4e201273 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ (k X0 x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e201257 X0
               have i₂ := b4e15 x
               grind)
            | exact superpose b4e15 b4e201257
            | (have j0 := b4e201257 X0
               grind)
            | exact resolve b4e201257 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e201257
          have b4e201564 : ∀ X0 : G, (k X0 x) = (τ (σ (M.op X0 x))) ∨ (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b4e14 (k X0 x)
               have i₂ := b4e201273 X0
               grind)
            | exact superpose b4e201273 b4e14
            | (have j1 := b4e201273 X0
               grind)
            | exact resolve b4e14 b4e201273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e201273
          have b4e201583 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b4e201564 X0
               have i₂ := b4e14 (M.op X0 x)
               grind)
            | exact superpose b4e14 b4e201564
            | (have j0 := b4e201564 X0
               grind)
            | exact resolve b4e201564 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e201564
          have b4e202055 : (M.op y x) = (k (M.op y x) x) ∨ (M.op (M.op y x) x) = (k (M.op y x) x) := by
            first
            | (have i₁ := b4e32447
               have i₂ := b4e201583 (M.op y x)
               grind)
            | exact superpose b4e201583 b4e32447
            | (have j1 := b4e201583 (M.op y x)
               grind)
            | exact resolve b4e32447 b4e201583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32447 b4e201583
          have b4e202141 : (M.op y (M.op y y)) = (k (M.op y x) x) ∨ (M.op y x) = (k (M.op y x) x) := by
            first
            | (have i₁ := b4e202055
               have i₂ := b4e13 y x
               grind)
            | exact superpose b4e13 b4e202055
            | exact resolve b4e202055 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e202055
          have b4e202239 : (M.op y x) = (k (M.op y x) x) ∨ (M.op y x) = (k (M.op y x) x) := by
            first
            | (have i₁ := b4e202141
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e202141
            | exact resolve b4e202141 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e202141
          have b4e202240 : (M.op y x) = (k (M.op y x) x) := by grind
          clear b4e202239
          have b4e203934 : ∀ X0 : G, (σ (M.op y x)) ≠ (σ (k y x)) ∨ (τ X0) = y ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e153
               have i₂ := b4e20585 X0 y x
               grind)
            | exact superpose b4e20585 b4e153
            | (have j1 := b4e20585 X0 y x
               grind)
            | exact resolve b4e153 b4e20585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20585
          have b4e203941 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (τ X0) = y := by
            intro X0
            first
            | (have j0 := b4e203934 X0
               have j1 := b4e177489 y X0 x
               grind)
            | (have r₁ := b4e203934 X0
               have r₂ := b4e177489 y x x
               grind)
            | exact resolve b4e203934 b4e177489
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e177489 b4e203934
          have b4e203982 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (τ (σ X0)) = y := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e203941 (σ X0)
               grind)
            | exact superpose b4e203941 b4e19
            | (have j1 := b4e203941 (σ X0)
               grind)
            | exact resolve b4e19 b4e203941
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e203941
          have b4e204026 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e203982 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e203982
            | (have j0 := b4e203982 X0
               grind)
            | exact resolve b4e203982 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e203982
          have b4e204197 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (M.op (σ (k X0 x)) (σ x)) ∨ y = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e33 (σ X0) X1 (σ x)
               have i₂ := b4e204026 X0
               grind)
            | exact superpose b4e204026 b4e33
            | (have j1 := b4e204026 X0
               grind)
            | exact resolve b4e33 b4e204026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e226115 : ∀ X0 : G, (M.op (M.op (σ (M.op y x)) X0) X0) = (M.op (σ (M.op y x)) (σ x)) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b4e204197 (M.op y x) X0
               have i₂ := b4e202240
               grind)
            | exact superpose b4e202240 b4e204197
            | (have j0 := b4e204197 (M.op y x) x
               grind)
            | exact resolve b4e204197 b4e202240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204197
          have b4e226194 : ∀ X0 : G, (M.op (M.op (σ (M.op y x)) X0) X0) = (M.op (σ (M.op y x)) (σ x)) := by
            intro X0
            first
            | (have j0 := b4e226115 X0
               grind)
            | (have r₁ := b4e226115 X0
               have r₂ := b4e37
               grind)
            | exact resolve b4e226115 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226115
          have b4e226225 : (σ (k (M.op y x) x)) = (M.op (σ (k (M.op y x) x)) (σ x)) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b4e226194 (σ x)
               have i₂ := b4e204026 (M.op y x)
               grind)
            | exact superpose b4e204026 b4e226194
            | (have j1 := b4e204026 (M.op y x)
               grind)
            | exact resolve b4e226194 b4e204026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204026
          have b4e226281 : (σ (k (M.op y x) x)) = (M.op (σ (k (M.op y x) x)) (σ x)) := by
            first
            | (have r₁ := b4e226225
               have r₂ := b4e37
               grind)
            | exact resolve b4e226225 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e226225
          have b4e226286 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ x)) := by
            first
            | (have i₁ := b4e226281
               have i₂ := b4e202240
               grind)
            | exact superpose b4e202240 b4e226281
            | exact resolve b4e226281 b4e202240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e202240 b4e226281
          have b4e242229 : ∀ X0 : G, (k X0 (τ (M.op (σ (M.op y x)) (σ x)))) = (τ (M.op (σ X0) (M.op (σ (M.op y x)) (σ x)))) := by
            intro X0
            first
            | (have i₁ := b4e45315 X0 (σ (M.op y x)) X0
               have i₂ := b4e226194 X0
               grind)
            | exact superpose b4e226194 b4e45315
            | exact resolve b4e45315 b4e226194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45315 b4e226194
          have b4e242321 : ∀ X0 : G, (τ (M.op (σ X0) (σ (M.op y x)))) = (k X0 (τ (σ (M.op y x)))) := by
            intro X0
            first
            | (have i₁ := b4e242229 X0
               have i₂ := b4e226286
               grind)
            | exact superpose b4e226286 b4e242229
            | exact resolve b4e242229 b4e226286
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226286 b4e242229
          have b4e242329 : ∀ X0 : G, (k X0 (M.op y x)) = (τ (M.op (σ X0) (σ (M.op y x)))) := by
            intro X0
            first
            | (have i₁ := b4e242321 X0
               have i₂ := b4e14 (M.op y x)
               grind)
            | exact superpose b4e14 b4e242321
            | exact resolve b4e242321 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242321
          have b4e242331 : ∀ X0 : G, (M.op X0 (M.op y x)) = (τ (M.op (σ X0) (σ (M.op y x)))) := by
            intro X0
            first
            | (have i₁ := b4e242329 X0
               have i₂ := b4e2414 X0
               grind)
            | exact superpose b4e2414 b4e242329
            | exact resolve b4e242329 b4e2414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2414 b4e242329
          have b4e242333 : ∀ X0 : G, (M.op (τ X0) (M.op y x)) = (τ (M.op X0 (σ (M.op y x)))) := by
            intro X0
            first
            | (have i₁ := b4e242331 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e242331
            | exact resolve b4e242331 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e242394 : (τ (M.op (σ y) (σ x))) = (M.op (τ (M.op (σ y) (σ (M.op y x)))) (M.op y x)) := by
            first
            | (have i₁ := b4e242333 (M.op (σ y) (σ (M.op y x)))
               have i₂ := b4e32 (σ (M.op y x))
               grind)
            | exact superpose b4e32 b4e242333
            | exact resolve b4e242333 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e242333
          have b4e242479 : (M.op (M.op y (M.op y x)) (M.op y x)) = (τ (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b4e242394
               have i₂ := b4e242331 y
               grind)
            | exact superpose b4e242331 b4e242394
            | exact resolve b4e242394 b4e242331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242331 b4e242394
          have b4e242496 : (M.op y (M.op y y)) = (τ (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b4e242479
               have i₂ := b4e13 y (M.op y x)
               grind)
            | exact superpose b4e13 b4e242479
            | exact resolve b4e242479 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242479
          have b4e242508 : (M.op y x) = (τ (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b4e242496
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e242496
            | exact resolve b4e242496 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242496
          have b4e242607 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e15 (M.op (σ y) (σ x))
               have i₂ := b4e242508
               grind)
            | exact superpose b4e242508 b4e15
            | exact resolve b4e15 b4e242508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242508
          have b4e242678 : False := by grind
          exact b4e242678
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e41 : y = (k x y) ∨ y = (M.op x y) := by grind
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
          have b5e53 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
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
          have b5e57 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e53 X0
               have j1 := b5e16 X0 (σ y)
               grind)
            | (have r₁ := b5e53 X0
               have r₂ := b5e16 X0 (σ y)
               grind)
            | exact resolve b5e53 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e152 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e57 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e153 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e152
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e152
            | exact resolve b5e152 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e152
          have b5e154 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e153
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e153
            | exact resolve b5e153 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e153
          have b5e155 : False := by grind
          exact b5e155
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e34 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e34
        have b6e38 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e37
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e37
          | exact resolve b6e37 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e41 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e13
          | exact resolve b6e13 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e42 : y = (k x y) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e41
          | exact resolve b6e41 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e50 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e42
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e42 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e57 : y = (M.op x y) ∨ x = (M.op y y) := by grind
        clear b6e50
        have b6e64 : x = (M.op y y) := by
          first
          | (have r₁ := b6e57
             have r₂ := b6e20
             grind)
          | exact resolve b6e57 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e68 : False := by grind
        exact b6e68
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e56 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b7e61 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e23
               grind)
            | exact resolve b7e56 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e64 : (σ y) = (σ (k x y)) := by
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
          have b7e68 : (k x y) = (τ (σ y)) := by
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
          have b7e69 : y = (k x y) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e68
            | exact resolve b7e68 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e98 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e99 : y = (M.op x y) ∨ x = (M.op y y) := by grind
          clear b7e98
          have b7e101 : x = (M.op y y) := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e21
               grind)
            | exact resolve b7e99 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e103 : False := by grind
          exact b7e103
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e81 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
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
          have b8e83 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e81 X0
               have j1 := b8e16 X0 (σ y)
               grind)
            | (have r₁ := b8e81 X0
               have r₂ := b8e16 X0 (σ y)
               grind)
            | exact resolve b8e81 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e137 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e83 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e138 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e137
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e137
            | exact resolve b8e137 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137
          have b8e157 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e138
               grind)
            | exact superpose b8e138 b8e20
            | exact resolve b8e20 b8e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e272 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e157
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e157
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e157 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157
          have b8e273 : x = (M.op y y) ∨ y = (M.op x y) := by grind
          clear b8e272
          have b8e276 : y = (M.op x y) := by
            first
            | (have r₁ := b8e273
               have r₂ := b8e22
               grind)
            | exact resolve b8e273 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e273
          have b8e277 : False := by grind
          exact b8e277

/-- `Equation4486`: `x ◇ (y ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e12
        | exact resolve b0e12 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X0 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op X0 X0) X3
           have i₂ := b0e11 (M.op X0 X0) X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (σ x)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ x) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e11 X2 X1 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (M.op X0 X0) (M.op X0 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 (M.op X0 X0) x
           have i₂ := b0e11 (M.op (M.op X0 X0) x) X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X0
           have i₂ := b0e41 X1
           grind)
        | exact superpose b0e41 b0e41
        | exact resolve b0e41 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op y x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e41 X1
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 y) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 y
           have i₂ := b0e46 X2 X0
           grind)
        | (have i₁ := b0e11 X1 X2 y
           have i₂ := b0e46 X0 X2
           grind)
        | exact superpose b0e46 b0e11
        | exact resolve b0e11 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e99 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e102 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e16 X2 X0
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X1 X0
           have j1 := b0e16 X2 X0
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X1 X1
           grind)
        | (have r₁ := b0e15 X0 (M.op X0 X0)
           have r₂ := b0e16 X0 (M.op (M.op X0 X0) (M.op X0 X0))
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e107 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e20
           have i₂ := b0e16 X0 (σ x)
           grind)
        | exact superpose b0e16 b0e20
        | (have j1 := b0e16 X0 (σ x)
           grind)
        | exact resolve b0e20 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e102 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e102
      have b0e167 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X0
           have i₂ := b0e40 X1
           grind)
        | exact superpose b0e40 b0e40
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e319 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e167 (σ x) X0
           grind)
        | (have i₁ := b0e18
           have i₂ := b0e167 X0 (σ x)
           grind)
        | exact superpose b0e167 b0e18
        | exact resolve b0e18 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e463 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 X1 (σ y)
           have i₂ := b0e167 (σ x) X0
           grind)
        | (have i₁ := b0e34 X1 (σ y)
           have i₂ := b0e167 X0 (σ x)
           grind)
        | exact superpose b0e167 b0e34
        | exact resolve b0e34 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e1150 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X2 X2) ∨ (k X2 (M.op (M.op X0 X0) (M.op X0 X0))) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X2 (M.op (M.op X0 X0) (M.op X0 X0))
           have i₂ := b0e43 X0 X1 (M.op (M.op X0 X0) (M.op X0 X0))
           grind)
        | exact superpose b0e43 b0e15
        | (have j0 := b0e15 (M.op X0 X0) (M.op X2 X2)
           grind)
        | exact resolve b0e15 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e1178 : ∀ X0 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X2 X2) ∨ (k X2 (M.op (M.op X0 X0) (M.op X0 X0))) = X2 := by
        intro X0 X2
        first
        | (have j0 := b0e1150 X0 x X2
           grind)
        | (have r₁ := b0e1150 x X2 X2
           have r₂ := b0e11 (M.op x x) x X2
           grind)
        | exact resolve b0e1150 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1150
      have b0e1260 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op (M.op y x) X0) ∨ (k X2 (M.op (M.op X0 X0) (M.op X0 X0))) = X2 := by
        intro X0 X2
        first
        | (have i₁ := b0e1178 X0 X2
           have i₂ := b0e49 (M.op X0 X0) X0
           grind)
        | exact superpose b0e49 b0e1178
        | (have j0 := b0e1178 X0 X2
           grind)
        | exact resolve b0e1178 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1178
      have b0e1309 : ∀ X0 X2 : G, (k X2 (M.op (M.op y x) X0)) = X2 ∨ (M.op X2 X2) = (M.op (M.op y x) X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e1260 X0 X2
           have i₂ := b0e49 (M.op X0 X0) X0
           grind)
        | exact superpose b0e49 b0e1260
        | (have j0 := b0e1260 X0 X2
           grind)
        | exact resolve b0e1260 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1260
      have b0e1399 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) = (M.op X2 (M.op (M.op y x) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e33 X0 y X2 X1
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e33
        | exact resolve b0e33 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1582 : ∀ X0 X2 : G, (M.op (M.op y x) X0) = (M.op X2 (M.op (M.op y x) X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e1399 X0 x X2
           have i₂ := b0e49 (M.op (M.op X0 X0) x) X0
           grind)
        | exact superpose b0e49 b0e1399
        | exact resolve b0e1399 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49 b0e1399
      have b0e1714 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e319 X1
           have i₂ := b0e46 x X0
           grind)
        | (have i₁ := b0e319 X1
           have i₂ := b0e46 X0 x
           grind)
        | exact superpose b0e46 b0e319
        | exact resolve b0e319 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e319
      have b0e2063 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e1714 x X0
           have i₂ := b0e41 x
           grind)
        | exact superpose b0e41 b0e1714
        | exact resolve b0e1714 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e2151 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e2063 x
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e2063
        | exact resolve b0e2063 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e2063
      have b0e2809 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op X1 X0) ∨ (M.op X3 X0) = (M.op X0 X4) ∨ (k X4 X0) = (M.op X4 X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e42 X0 X0 X2
           have i₂ := b0e99 X0 X1 X2
           grind)
        | exact superpose b0e99 b0e42
        | (have j1 := b0e99 X0 X3 X4
           grind)
        | exact resolve b0e42 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e99
      have b0e3418 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 x
           have i₂ := b0e107 (σ X0)
           grind)
        | exact superpose b0e107 b0e17
        | (have j1 := b0e107 (σ X0)
           grind)
        | exact resolve b0e17 b0e107
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107
      have b0e4773 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e111 X1 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111
      have b0e4777 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e4773 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4773
      have b0e5993 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e108 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108
      have b0e5994 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e5993 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5993
      have b0e9039 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 y) X1) = (M.op X3 (M.op (M.op X1 X4) X1)) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e33 X1 X4 X3 x
           have i₂ := b0e79 X0 (M.op (M.op X1 X1) x) X1
           grind)
        | exact superpose b0e79 b0e33
        | exact resolve b0e33 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e28798 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) X1) = (M.op X2 (M.op (M.op X0 y) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1582 (M.op X2 X2) X2
           have i₂ := b0e79 X0 (M.op y x) X2
           grind)
        | exact superpose b0e79 b0e1582
        | exact resolve b0e1582 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79 b0e1582
      have b0e122822 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      clear b0e4777
      have b0e123175 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e122822 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e122822
      have b0e123445 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e123175 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123175
      have b0e124658 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ (M.op X1 (σ y)) ∨ (M.op X1 (σ y)) = (k (M.op X1 (σ y)) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e123445 (M.op X1 (σ y)) (σ x)
           have i₂ := b0e463 X1 X0
           grind)
        | exact superpose b0e463 b0e123445
        | (have j0 := b0e123445 (M.op X1 (σ y)) (σ x)
           grind)
        | (have r₁ := b0e123445 (M.op (M.op X0 (σ y)) (σ x)) (σ y)
           have r₂ := b0e463 X0 (M.op (M.op X0 (σ y)) (σ x))
           grind)
        | (have r₁ := b0e123445 (M.op X1 (σ y)) (σ x)
           have r₂ := b0e463 X1 X1
           grind)
        | exact resolve b0e123445 b0e463
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e463 b0e123445
      have b0e124723 : ∀ X1 : G, (M.op X1 (σ y)) = (k (M.op X1 (σ y)) (σ x)) := by
        intro X1
        first
        | (have j0 := b0e124658 x X1
           grind)
        | (have r₁ := b0e124658 x X1
           have r₂ := b0e167 x X1
           grind)
        | (have r₁ := b0e124658 X1 x
           have r₂ := b0e167 x X1
           grind)
        | exact resolve b0e124658 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e167 b0e124658
      have b0e128028 : ∀ X0 X1 : G, (k X1 (M.op (M.op y x) X0)) = X1 ∨ (k X1 (M.op (M.op y x) X0)) = X1 := by
        intro X0 X1
        grind
      clear b0e1309
      have b0e128701 : ∀ X0 X1 : G, (k X1 (M.op (M.op y x) X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e128028 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128028
      have b0e129395 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 y) X1)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e128701 (M.op (M.op X1 x) X1) X2
           have i₂ := b0e9039 X0 X1 (M.op y x) x
           grind)
        | exact superpose b0e9039 b0e128701
        | exact resolve b0e128701 b0e9039
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9039 b0e128701
      have b0e240567 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X3 X1) ∨ (M.op X0 X1) = (M.op X3 X1) ∨ (k X2 X1) = (M.op X2 X1) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e2809 X1 X3 X0 X3 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e240588 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 X1) ∨ (k X2 X1) = (M.op X2 X1) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e240567 X0 X1 X2 X3
           have j1 := b0e2809 X1 X3 X0 X3 X2
           grind)
        | (have r₁ := b0e240567 X0 X0 X0 X1
           have r₂ := b0e2809 X0 X1 X0 X3 x
           grind)
        | (have r₁ := b0e240567 X0 X0 X0 X2
           have r₂ := b0e2809 X0 X0 X2 X3 x
           grind)
        | (have r₁ := b0e240567 X0 x X0 X0
           have r₂ := b0e2809 X0 X1 X2 x x
           grind)
        | exact resolve b0e240567 b0e2809
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2809 b0e240567
      have b0e261493 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (k (τ (M.op X0 (σ y))) x) := by
        intro X0
        first
        | (have i₁ := b0e31 (M.op X0 (σ y)) x
           have i₂ := b0e124723 X0
           grind)
        | exact superpose b0e124723 b0e31
        | exact resolve b0e31 b0e124723
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e124723
      have b0e463716 : ∀ X0 X1 : G, y = (M.op X0 x) ∨ (k X1 x) = (M.op X1 x) := by
        intro X0 X1
        first
        | (have i₁ := b0e19
           have i₂ := b0e240588 x x X1 X0
           grind)
        | (have i₁ := b0e19
           have i₂ := b0e240588 X0 x X1 x
           grind)
        | exact superpose b0e240588 b0e19
        | (have j1 := b0e240588 X0 x X1 x
           grind)
        | exact resolve b0e19 b0e240588
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e240588
      have b0e468083 : ∀ X1 X2 : G, y = (M.op X1 y) ∨ (k X2 x) = (M.op X2 x) := by
        intro X1 X2
        first
        | (have i₁ := b0e28798 x x X2
           have i₂ := b0e463716 (M.op x y) X1
           grind)
        | exact superpose b0e463716 b0e28798
        | (have j1 := b0e463716 x X2
           grind)
        | exact resolve b0e28798 b0e463716
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28798
      have b0e468087 : ∀ X0 X2 : G, (k X0 y) = X0 ∨ (k X2 x) = (M.op X2 x) := by
        intro X0 X2
        first
        | (have i₁ := b0e129395 x x X0
           have i₂ := b0e463716 (M.op x y) X2
           grind)
        | exact superpose b0e463716 b0e129395
        | (have j1 := b0e463716 X0 X2
           grind)
        | exact resolve b0e129395 b0e463716
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129395 b0e463716
      have b0e469483 : ∀ X0 X2 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (k X2 x) = (M.op X2 x) := by
        intro X0 X2
        first
        | (have i₁ := b0e1714 x X0
           have i₂ := b0e468083 x X2
           grind)
        | exact superpose b0e468083 b0e1714
        | (have j1 := b0e468083 x X2
           grind)
        | exact resolve b0e1714 b0e468083
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1714 b0e468083
      have b0e471771 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e5994 y
           have i₂ := b0e468087 y X0
           grind)
        | exact superpose b0e468087 b0e5994
        | (have j0 := b0e5994 y
           have j1 := b0e468087 X0 X0
           grind)
        | exact resolve b0e5994 b0e468087
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5994 b0e468087
      have b0e471841 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b0e471771 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e471771
      have b0e471854 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b0e471841 X0
           have j1 := b0e469483 X0 X0
           grind)
        | (have r₁ := b0e471841 X0
           have r₂ := b0e469483 (σ y) x
           grind)
        | exact resolve b0e471841 b0e469483
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e469483 b0e471841
      have b0e475932 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (M.op (τ (M.op X0 (σ y))) x) := by
        intro X0
        first
        | (have i₁ := b0e261493 X0
           have i₂ := b0e471854 (τ (M.op X0 (σ y)))
           grind)
        | exact superpose b0e471854 b0e261493
        | exact resolve b0e261493 b0e471854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e261493
      have b0e493218 : (τ (σ x)) = (M.op (τ (σ x)) x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e475932 (σ y)
           have i₂ := b0e3418 y
           grind)
        | exact superpose b0e3418 b0e475932
        | (have j1 := b0e3418 y
           grind)
        | exact resolve b0e475932 b0e3418
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3418 b0e475932
      have b0e493387 : x = (M.op x x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e493218
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e493218
        | exact resolve b0e493218 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e493218
      have b0e493450 : x = y ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e493387
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e493387
        | exact resolve b0e493387 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e493387
      have b0e493457 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e493450
           have i₂ := b0e471854 y
           grind)
        | exact superpose b0e471854 b0e493450
        | exact resolve b0e493450 b0e471854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e471854 b0e493450
      have b0e493458 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b0e493457
           have r₂ := b0e2151
           grind)
        | exact resolve b0e493457 b0e2151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e493457
      have b0e497011 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e493458
           grind)
        | exact superpose b0e493458 b0e12
        | exact resolve b0e12 b0e493458
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e493458
      have b0e497047 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e497011
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e497011
        | exact resolve b0e497011 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e497011
      have b0e497048 : x = y := by grind
      clear b0e497047
      have b0e501112 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e2151
           have i₂ := b0e497048
           grind)
        | exact superpose b0e497048 b0e2151
        | exact resolve b0e2151 b0e497048
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2151 b0e497048
      have b0e501352 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e501112
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e501112
        | exact resolve b0e501112 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e501112
      have b0e501407 : False := by grind
      exact b0e501407
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ y) = (k (σ y) (σ y)) := by grind
        have b1e26 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e25
          | exact resolve b1e25 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e31 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : y = (k y y) := by
          first
          | (have i₁ := b1e31
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e31
          | exact resolve b1e31 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e42 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e42 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e42
          | exact resolve b1e42 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e49 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e43 X0
             have i₂ := b1e43 X1
             grind)
          | exact superpose b1e43 b1e43
          | exact resolve b1e43 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e47 (σ x)
             grind)
          | exact superpose b1e47 b1e19
          | exact resolve b1e19 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e66 : (σ y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e64
             have i₂ := b1e43 x
             grind)
          | exact superpose b1e43 b1e64
          | exact resolve b1e64 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e96 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e32
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e32 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e99 : y = (M.op y y) := by grind
        clear b1e96
        have b1e156 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e99
             have i₂ := b1e49 y X0
             grind)
          | (have i₁ := b1e99
             have i₂ := b1e49 X0 y
             grind)
          | exact superpose b1e49 b1e99
          | exact resolve b1e99 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e99
        have b1e186 : y = (M.op y x) := by
          first
          | (have i₁ := b1e43 x
             have i₂ := b1e156 x
             grind)
          | exact superpose b1e156 b1e43
          | exact resolve b1e43 b1e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e156
        have b1e312 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e66
             have i₂ := b1e186
             grind)
          | exact superpose b1e186 b1e66
          | exact resolve b1e66 b1e186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e186
        have b1e314 : False := by grind
        exact b1e314
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e79 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e154 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e1925 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e79 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e1926 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1925
             have r₂ := b2e22
             grind)
          | exact resolve b2e1925 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1925
        have b2e1927 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1926
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1926
          | exact resolve b2e1926 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1926
        have b2e1928 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1927
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1927
          | exact resolve b2e1927 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1927
        have b2e3056 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e154
        have b2e3070 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e3056 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e3056
          | exact resolve b2e3056 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3056
        have b2e6395 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e89 x x
             grind)
          | exact superpose b2e89 b2e21
          | (have j1 := b2e89 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e89 x y
             grind)
          | exact resolve b2e21 b2e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e6574 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e6395
        have b2e53875 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e6574
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e6574
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e6574 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6574
        have b2e53885 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e53875
        have b2e53902 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e53885
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e53885
          | exact resolve b2e53885 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53885
        have b2e53903 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e53902
        have b2e53915 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e53903
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e53903
          | exact resolve b2e53903 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53903
        have b2e53940 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e3070 x
             have i₂ := b2e53915
             grind)
          | exact superpose b2e53915 b2e3070
          | exact resolve b2e3070 b2e53915
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3070 b2e53915
        have b2e54058 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e53940
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e53940
          | exact resolve b2e53940 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53940
        have b2e57990 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e54058
             grind)
          | exact superpose b2e54058 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e54058
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54058
        have b2e58003 : x = (M.op x x) ∨ x = y := by grind
        clear b2e57990
        have b2e58032 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e58003
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e58003
          | exact resolve b2e58003 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58003
        have b2e58033 : x = y := by grind
        clear b2e58032
        have b2e60452 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1928
             have i₂ := b2e58033
             grind)
          | exact superpose b2e58033 b2e1928
          | exact resolve b2e1928 b2e58033
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1928 b2e58033
        have b2e60476 : False := by grind
        exact b2e60476
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e43 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e43 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e43
          | exact resolve b3e43 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e51 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y
             have i₂ := b3e47 X1
             grind)
          | exact superpose b3e47 b3e12
          | exact resolve b3e12 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e58 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e105 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X0) = (M.op X2 X2) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X0 X0) X0 X1
             have i₂ := b3e17 X2 (M.op X0 X0)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 (M.op (M.op X0 X1) X0)
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e114 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X0)) = (M.op y X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X0) = (M.op X2 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e105 X0 X1 X2
             have i₂ := b3e51 X2 X0
             grind)
          | exact superpose b3e51 b3e105
          | (have j0 := b3e105 X0 X1 X2
             grind)
          | exact resolve b3e105 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105
        have b3e121 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e51 X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e51
          | exact resolve b3e51 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e127 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op X0 X2) X0) := by
          intro X0 X2
          first
          | (have i₁ := b3e12 x X0 X2
             have i₂ := b3e51 x X0
             grind)
          | exact superpose b3e51 b3e12
          | exact resolve b3e12 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e164 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e121 (σ x)
             grind)
          | exact superpose b3e121 b3e19
          | exact resolve b3e19 b3e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e169 : (σ y) ≠ (M.op y (σ x)) := by
          first
          | (have i₁ := b3e164
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e164
          | exact resolve b3e164 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e164
        have b3e185 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e169
             have i₂ := b3e121 X0
             grind)
          | exact superpose b3e121 b3e169
          | exact resolve b3e169 b3e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e121
        have b3e221 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          grind
        clear b3e59
        have b3e231 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e221 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e221
        have b3e238 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e27 X0 y
             have i₂ := b3e231 (τ X0)
             grind)
          | exact superpose b3e231 b3e27
          | exact resolve b3e27 b3e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e231
        have b3e239 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e238 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e238
          | exact resolve b3e238 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e238
        have b3e7458 : ∀ X0 X1 : G, (M.op X0 X0) = (σ y) ∨ (M.op y (σ x)) = (k X0 (σ y)) ∨ (σ y) = (M.op (M.op (σ x) X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e114 (σ x) X1 x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e114
          | exact resolve b3e114 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114
        have b3e7853 : ∀ X0 X1 : G, (M.op y (σ x)) = X0 ∨ (M.op X0 X0) = (σ y) ∨ (σ y) = (M.op (M.op (σ x) X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e7458 X0 X1
             have i₂ := b3e239 X0
             grind)
          | exact superpose b3e239 b3e7458
          | (have j0 := b3e7458 X0 X1
             grind)
          | exact resolve b3e7458 b3e239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e239 b3e7458
        have b3e8000 : ∀ X0 : G, (σ y) = (M.op y (σ x)) ∨ (M.op y (σ x)) = X0 ∨ (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e7853 X0 x
             have i₂ := b3e127 (σ x) x
             grind)
          | exact superpose b3e127 b3e7853
          | (have j0 := b3e7853 X0 x
             grind)
          | exact resolve b3e7853 b3e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e127 b3e7853
        have b3e8072 : ∀ X0 : G, (M.op y (σ x)) = X0 ∨ (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have j0 := b3e8000 X0
             grind)
          | (have r₁ := b3e8000 X0
             have r₂ := b3e169
             grind)
          | (have r₁ := b3e8000 (σ y)
             have r₂ := b3e169
             grind)
          | exact resolve b3e8000 b3e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8000
        have b3e10047 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op y (σ x)) := by
          first
          | (have i₁ := b3e185 (σ y)
             have i₂ := b3e8072 (σ y)
             grind)
          | exact superpose b3e8072 b3e185
          | (have j1 := b3e8072 (σ y)
             grind)
          | (have r₁ := b3e185 (σ y)
             have r₂ := b3e8072 (σ y)
             grind)
          | exact resolve b3e185 b3e8072
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e185 b3e8072
        have b3e10066 : (σ y) = (M.op y (σ x)) := by grind
        clear b3e10047
        have b3e10083 : False := by grind
        exact b3e10083
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e45 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e45
            | exact resolve b4e45 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e50 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e44 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e44
            | exact resolve b4e44 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e71 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e50 (σ x)
               grind)
            | exact superpose b4e50 b4e20
            | exact resolve b4e20 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e73 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e71
               have i₂ := b4e49 x
               grind)
            | exact superpose b4e49 b4e71
            | exact resolve b4e71 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e71
          have b4e74 : False := by grind
          exact b4e74
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b5e39 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e39 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e39
            | exact resolve b5e39 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e49 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 y
               have i₂ := b5e45 X1
               grind)
            | exact superpose b5e45 b5e13
            | exact resolve b5e13 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e55 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e45 y
               grind)
            | exact superpose b5e45 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e45 y
               grind)
            | exact resolve b5e17 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e55 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e92 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e93 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X1 X1) X1 X2
               have i₂ := b5e18 (M.op X1 X1) X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X0 (M.op X1 X1))
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e102 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e107 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e102 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e122 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op X0 X2) X0) := by
            intro X0 X2
            first
            | (have i₁ := b5e13 x X0 X2
               have i₂ := b5e49 x X0
               grind)
            | exact superpose b5e49 b5e13
            | exact resolve b5e13 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1170 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            grind
          clear b5e56
          have b5e1197 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e1170 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1170
          have b5e1298 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e1197 (τ X0)
               grind)
            | exact superpose b5e1197 b5e27
            | exact resolve b5e27 b5e1197
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e1197
          have b5e1299 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1298 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1298
            | exact resolve b5e1298 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1298
          have b5e2782 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e20
               have i₂ := b5e92 (σ y) (σ x) X0
               grind)
            | (have i₁ := b5e20
               have i₂ := b5e92 (σ x) x (σ y)
               grind)
            | exact superpose b5e92 b5e20
            | (have j1 := b5e92 (σ y) x X0
               grind)
            | exact resolve b5e20 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92
          have b5e2969 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e2782 X0
               grind)
            | (have r₁ := b5e2782 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e2782 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2782
          have b5e3068 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e2969 X0
               have i₂ := b5e45 x
               grind)
            | exact superpose b5e45 b5e2969
            | (have j0 := b5e2969 X0
               grind)
            | exact resolve b5e2969 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45 b5e2969
          have b5e3122 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e3068 X0
               have i₂ := b5e1299 X0
               grind)
            | exact superpose b5e1299 b5e3068
            | (have j0 := b5e3068 X0
               grind)
            | exact resolve b5e3068 b5e1299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3068
          have b5e5591 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ y)) ∨ (σ y) = (M.op (M.op X0 X1) X0) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1299 (M.op X0 X0)
               have i₂ := b5e93 (σ y) X0 X1
               grind)
            | exact superpose b5e93 b5e1299
            | (have j1 := b5e93 (σ y) X0 X1
               grind)
            | exact resolve b5e1299 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e5606 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ y)) ∨ (σ y) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b5e5591 X0 X1
               grind)
            | (have r₁ := b5e5591 X0 X1
               have r₂ := b5e24
               grind)
            | exact resolve b5e5591 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5591
          have b5e5762 : ∀ X0 : G, (σ y) = (M.op y X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e5606 X0 x
               have i₂ := b5e122 X0 x
               grind)
            | exact superpose b5e122 b5e5606
            | (have j0 := b5e5606 X0 x
               grind)
            | exact resolve b5e5606 b5e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e122 b5e5606
          have b5e8041 : ∀ X0 : G, (σ y) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e3122 (M.op X0 X0)
               have i₂ := b5e49 (σ y) X0
               grind)
            | exact superpose b5e49 b5e3122
            | (have j0 := b5e3122 (M.op X0 X0)
               grind)
            | exact resolve b5e3122 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e3122
          have b5e8053 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e8041 X0
               have j1 := b5e5762 X0
               grind)
            | (have r₁ := b5e8041 X0
               have r₂ := b5e5762 X0
               grind)
            | exact resolve b5e8041 b5e5762
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5762 b5e8041
          have b5e8097 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e8053 X0
               have i₂ := b5e107 X0
               grind)
            | exact superpose b5e107 b5e8053
            | (have j1 := b5e107 (σ y)
               grind)
            | exact resolve b5e8053 b5e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e107 b5e8053
          have b5e8204 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e8097 X0
               grind)
            | (have r₁ := b5e8097 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e8097 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8097
          have b5e8234 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e8204 X0
               have i₂ := b5e1299 X0
               grind)
            | exact superpose b5e1299 b5e8204
            | exact resolve b5e8204 b5e1299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1299 b5e8204
          have b5e8924 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e8234 (σ y)
               grind)
            | exact superpose b5e8234 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e8234 (σ y)
               grind)
            | exact resolve b5e24 b5e8234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8234
          have b5e8930 : False := by grind
          exact b5e8930
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ x) = (σ (k x y)) := by
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
        have b6e44 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e61 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e44 X0
             have i₂ := b6e44 X1
             grind)
          | exact superpose b6e44 b6e44
          | exact resolve b6e44 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b6e92 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e25
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e25 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e94 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e92
             have r₂ := b6e20
             grind)
          | exact resolve b6e92 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e97 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e94
             have r₂ := b6e21
             grind)
          | exact resolve b6e94 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e94
        have b6e236 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e61 (σ x) X0
             grind)
          | (have i₁ := b6e19
             have i₂ := b6e61 X0 (σ x)
             grind)
          | exact superpose b6e61 b6e19
          | exact resolve b6e19 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e237 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e236 X0
             have i₂ := b6e97
             grind)
          | exact superpose b6e97 b6e236
          | exact resolve b6e236 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97 b6e236
        have b6e284 : (σ x) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e237 x
             have i₂ := b6e44 x
             grind)
          | exact superpose b6e44 b6e237
          | exact resolve b6e237 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e237
        have b6e4212 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e89 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e89
          | exact resolve b6e89 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e4490 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e4212
        have b6e5953 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e4490
             grind)
          | exact superpose b6e4490 b6e13
          | exact resolve b6e13 b6e4490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5970 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e5953
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e5953
          | exact resolve b6e5953 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5953
        have b6e6354 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e5970
             grind)
          | exact superpose b6e5970 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e5970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5970
        have b6e6364 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e6354
        have b6e6374 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e6364
             have r₂ := b6e20
             grind)
          | exact resolve b6e6364 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6364
        have b6e6606 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e6374
        have b6e7695 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4490
             have i₂ := b6e6606
             grind)
          | exact superpose b6e6606 b6e4490
          | exact resolve b6e4490 b6e6606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4490 b6e6606
        have b6e7710 : (σ x) = (σ y) := by grind
        clear b6e7695
        have b6e7847 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e7710
             grind)
          | exact superpose b6e7710 b6e22
          | exact resolve b6e22 b6e7710
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e7856 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e284
             have i₂ := b6e7710
             grind)
          | exact superpose b6e7710 b6e284
          | exact resolve b6e284 b6e7710
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e284 b6e7710
        have b6e7878 : False := by grind
        exact b6e7878
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ y) = (k (σ y) (σ y)) := by grind
          have b7e27 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e26
            | exact resolve b7e26 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e32 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e27
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : y = (k y y) := by
            first
            | (have i₁ := b7e32
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e32
            | exact resolve b7e32 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e85 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e18 y y
               grind)
            | exact superpose b7e18 b7e33
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e33 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e88 : y = (M.op y y) := by grind
          clear b7e85
          have b7e92 : False := by grind
          exact b7e92
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1339 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e1340 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1339
               have r₂ := b8e24
               grind)
            | exact resolve b8e1339 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1339
          have b8e1341 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1340
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1340
            | exact resolve b8e1340 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1340
          have b8e1342 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1341
               grind)
            | exact superpose b8e1341 b8e20
            | exact resolve b8e20 b8e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1341
          have b8e1356 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1342
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1342
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1342 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1342
          have b8e1357 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e1356
          have b8e1360 : y = (M.op y y) := by
            first
            | (have r₁ := b8e1357
               have r₂ := b8e21
               grind)
            | exact resolve b8e1357 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1357
          have b8e1363 : False := by grind
          exact b8e1363

/-- `Equation4546`: `x ◇ (y ◇ z) = (z ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4546 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4546 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4546.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e12
        | exact resolve b0e12 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X3) (M.op X1 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X3 (M.op X1 X0)
           have i₂ := b0e11 X3 X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X3)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op X1 X0) X3
           have i₂ := b0e11 X3 X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e11 X3 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op X3 (M.op X1 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X3 (M.op X1 X0)
           have i₂ := b0e11 (M.op (M.op X1 X0) X3) X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e33 X0 X1 X2 x
           have i₂ := b0e11 (M.op (M.op X1 X0) x) X1 X0
           grind)
        | exact superpose b0e11 b0e33
        | exact resolve b0e33 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e48 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X0
           have i₂ := b0e41 X1
           grind)
        | exact superpose b0e41 b0e41
        | exact resolve b0e41 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e93 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e96 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e16 X2 X0
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X1 X0
           have j1 := b0e16 X2 X0
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X1 X1
           grind)
        | (have r₁ := b0e15 X0 (M.op X0 X0)
           have r₂ := b0e16 X0 (M.op (M.op X0 X0) (M.op X0 X0))
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e101 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e20
           have i₂ := b0e16 X0 (σ x)
           grind)
        | exact superpose b0e16 b0e20
        | (have j1 := b0e16 X0 (σ x)
           grind)
        | exact resolve b0e20 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e105 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e96 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96
      have b0e124 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X0
           have i₂ := b0e40 X1
           grind)
        | exact superpose b0e40 b0e40
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e297 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 (M.op X1 X0)) ∨ (M.op X2 (M.op X1 X0)) = (M.op X3 X3) ∨ (k X3 (M.op X2 (M.op X1 X0))) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e15 X3 (M.op X2 (M.op X1 X0))
           have i₂ := b0e43 X0 X1 (M.op X2 (M.op X1 X0)) X2
           grind)
        | exact superpose b0e43 b0e15
        | (have j0 := b0e15 X3 (M.op X2 (M.op X1 X0))
           grind)
        | exact resolve b0e15 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e304 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op X3 X3) ∨ (k X3 (M.op X2 (M.op X1 X0))) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e297 X0 X1 X2 X3
           grind)
        | (have r₁ := b0e297 X2 X1 X0 X3
           have r₂ := b0e11 X0 X1 X2
           grind)
        | exact resolve b0e297 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e297
      have b0e362 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) X2)) = (M.op (M.op X0 (σ y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 (σ y) X2
           have i₂ := b0e124 X2 X0
           grind)
        | (have i₁ := b0e11 X1 (σ y) X2
           have i₂ := b0e124 X0 X2
           grind)
        | exact superpose b0e124 b0e11
        | exact resolve b0e11 b0e124
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e364 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X1 (M.op X2 (σ y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (σ y)
           have i₂ := b0e124 (M.op (σ y) X2) X0
           grind)
        | (have i₁ := b0e11 X1 X2 (σ y)
           have i₂ := b0e124 X0 (M.op (σ y) X2)
           grind)
        | exact superpose b0e124 b0e11
        | exact resolve b0e11 b0e124
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e365 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e124 (σ x) X0
           grind)
        | (have i₁ := b0e18
           have i₂ := b0e124 X0 (σ x)
           grind)
        | exact superpose b0e124 b0e18
        | exact resolve b0e18 b0e124
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e514 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X4 (M.op (M.op X0 (M.op X1 X2)) X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e46 X0 (M.op X1 X2) X2
           have i₂ := b0e42 X0 X1 X2 X3
           grind)
        | (have i₁ := b0e46 X3 (M.op X1 X2) X2
           have i₂ := b0e42 X0 X1 X2 X3
           grind)
        | exact superpose b0e42 b0e46
        | exact resolve b0e46 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e607 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e365 X1
           have i₂ := b0e48 x X0
           grind)
        | (have i₁ := b0e365 X1
           have i₂ := b0e48 X0 x
           grind)
        | exact superpose b0e48 b0e365
        | exact resolve b0e365 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e365
      have b0e1180 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) = (M.op X4 (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e46 X2 (M.op (M.op X1 X0) X3) X2
           have i₂ := b0e38 X0 X1 X2 X3
           grind)
        | exact superpose b0e38 b0e46
        | exact resolve b0e46 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e1380 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e607 x X0
           have i₂ := b0e41 x
           grind)
        | exact superpose b0e41 b0e607
        | exact resolve b0e607 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e1564 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e1380 x
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e1380
        | exact resolve b0e1380 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1380
      have b0e1929 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X3 X0) = (M.op X0 X4) ∨ (k X4 X0) = (M.op X4 X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e42 X0 X0 X0 X3
           have i₂ := b0e93 X0 X1 X2
           grind)
        | exact superpose b0e93 b0e42
        | (have j1 := b0e93 X0 X3 X4
           grind)
        | exact resolve b0e42 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e93
      have b0e2362 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 x
           have i₂ := b0e101 (σ X0)
           grind)
        | exact superpose b0e101 b0e17
        | (have j1 := b0e101 (σ X0)
           grind)
        | exact resolve b0e17 b0e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e101
      have b0e2637 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e105 X1 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105
      have b0e2641 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e2637 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2637
      have b0e3373 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e102 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e102
      have b0e3374 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e3373 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3373
      have b0e6448 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (M.op (σ y) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e364 X0 X1 x
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e364
        | exact resolve b0e364 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e364
      have b0e12073 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e6448 X1 x
           have i₂ := b0e362 X0 x (σ x)
           grind)
        | exact superpose b0e362 b0e6448
        | exact resolve b0e6448 b0e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e362 b0e6448
      have b0e72678 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      clear b0e2641
      have b0e72979 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e72678 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72678
      have b0e74355 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e72979 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72979
      have b0e74970 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ (M.op X1 (σ y)) ∨ (M.op X1 (σ y)) = (k (M.op X1 (σ y)) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e74355 (M.op X1 (σ y)) (σ x)
           have i₂ := b0e12073 X1 X0
           grind)
        | exact superpose b0e12073 b0e74355
        | (have j0 := b0e74355 (M.op X1 (σ y)) (σ x)
           grind)
        | (have r₁ := b0e74355 (M.op (M.op X0 (σ y)) (σ x)) (σ y)
           have r₂ := b0e12073 X0 (M.op (M.op X0 (σ y)) (σ x))
           grind)
        | (have r₁ := b0e74355 (M.op X1 (σ y)) (σ x)
           have r₂ := b0e12073 X1 X1
           grind)
        | exact resolve b0e74355 b0e12073
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12073 b0e74355
      have b0e75003 : ∀ X1 : G, (M.op X1 (σ y)) = (k (M.op X1 (σ y)) (σ x)) := by
        intro X1
        first
        | (have j0 := b0e74970 x X1
           grind)
        | (have r₁ := b0e74970 x X1
           have r₂ := b0e124 x X1
           grind)
        | (have r₁ := b0e74970 X1 x
           have r₂ := b0e124 x X1
           grind)
        | exact resolve b0e74970 b0e124
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e124 b0e74970
      have b0e78110 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X0 (M.op X1 X2))) = X3 ∨ (k X3 (M.op X0 (M.op X1 X2))) = X3 := by
        intro X0 X1 X2 X3
        grind
      clear b0e304
      have b0e78396 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X0 (M.op X1 X2))) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e78110 X0 X1 X2 X3
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78110
      have b0e78730 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e78396 x (M.op X0 X1) X0 X2
           have i₂ := b0e46 X0 X1 x
           grind)
        | exact superpose b0e46 b0e78396
        | exact resolve b0e78396 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e78396
      have b0e94726 : ∀ X0 X1 X2 X3 X4 X5 : G, (k X4 (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X5)) = X4 := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e78730 X5 (M.op (M.op X0 (M.op X1 X2)) X3) X4
           have i₂ := b0e514 X0 X1 X2 X3 X5
           grind)
        | exact superpose b0e514 b0e78730
        | exact resolve b0e78730 b0e514
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e514 b0e78730
      have b0e181938 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X3 X1) ∨ (M.op X0 X1) = (M.op X3 X1) ∨ (M.op X2 X1) = (k X2 X1) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e1929 X1 X0 X3 X3 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e181957 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 X1) ∨ (M.op X2 X1) = (k X2 X1) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e181938 X0 X1 X2 X3
           have j1 := b0e1929 X1 X0 X3 X3 X2
           grind)
        | (have r₁ := b0e181938 X0 X0 X0 X2
           have r₂ := b0e1929 X0 X0 X2 X3 x
           grind)
        | (have r₁ := b0e181938 X0 X0 X0 X1
           have r₂ := b0e1929 X0 X1 X0 X3 x
           grind)
        | (have r₁ := b0e181938 X0 x X0 X0
           have r₂ := b0e1929 X0 X1 X2 x x
           grind)
        | exact resolve b0e181938 b0e1929
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1929 b0e181938
      have b0e220600 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (k (τ (M.op X0 (σ y))) x) := by
        intro X0
        first
        | (have i₁ := b0e31 (M.op X0 (σ y)) x
           have i₂ := b0e75003 X0
           grind)
        | exact superpose b0e75003 b0e31
        | exact resolve b0e31 b0e75003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e75003
      have b0e471508 : ∀ X0 X1 : G, y = (M.op X0 x) ∨ (k X1 x) = (M.op X1 x) := by
        intro X0 X1
        first
        | (have i₁ := b0e19
           have i₂ := b0e181957 x x X1 X0
           grind)
        | (have i₁ := b0e19
           have i₂ := b0e181957 X0 x X1 x
           grind)
        | exact superpose b0e181957 b0e19
        | (have j1 := b0e181957 X0 x X1 x
           grind)
        | exact resolve b0e19 b0e181957
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e181957
      have b0e476423 : ∀ X3 X4 : G, y = (M.op X3 y) ∨ (M.op X4 x) = (k X4 x) := by
        intro X3 X4
        first
        | (have i₁ := b0e1180 x x x x X4
           have i₂ := b0e471508 (M.op (M.op (M.op x x) x) x) x
           grind)
        | exact superpose b0e471508 b0e1180
        | (have j1 := b0e471508 x X4
           grind)
        | exact resolve b0e1180 b0e471508
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1180
      have b0e476431 : ∀ X0 X5 : G, (k X0 y) = X0 ∨ (k X5 x) = (M.op X5 x) := by
        intro X0 X5
        first
        | (have i₁ := b0e94726 x x x x X0 x
           have i₂ := b0e471508 (M.op (M.op x (M.op x x)) x) X5
           grind)
        | exact superpose b0e471508 b0e94726
        | (have j1 := b0e471508 X0 X5
           grind)
        | exact resolve b0e94726 b0e471508
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e94726 b0e471508
      have b0e480577 : ∀ X0 X2 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (k X2 x) = (M.op X2 x) := by
        intro X0 X2
        first
        | (have i₁ := b0e607 x X0
           have i₂ := b0e476423 x X2
           grind)
        | exact superpose b0e476423 b0e607
        | (have j1 := b0e476423 x X2
           grind)
        | exact resolve b0e607 b0e476423
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e607 b0e476423
      have b0e481929 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e3374 y
           have i₂ := b0e476431 y X0
           grind)
        | exact superpose b0e476431 b0e3374
        | (have j0 := b0e3374 y
           have j1 := b0e476431 X0 X0
           grind)
        | exact resolve b0e3374 b0e476431
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3374 b0e476431
      have b0e481999 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 x) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b0e481929 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e481929
      have b0e482012 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b0e481999 X0
           have j1 := b0e480577 X0 X0
           grind)
        | (have r₁ := b0e481999 X0
           have r₂ := b0e480577 (σ y) x
           grind)
        | exact resolve b0e481999 b0e480577
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e480577 b0e481999
      have b0e484172 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (M.op (τ (M.op X0 (σ y))) x) := by
        intro X0
        first
        | (have i₁ := b0e220600 X0
           have i₂ := b0e482012 (τ (M.op X0 (σ y)))
           grind)
        | exact superpose b0e482012 b0e220600
        | exact resolve b0e220600 b0e482012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e220600
      have b0e498300 : (τ (σ x)) = (M.op (τ (σ x)) x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e484172 (σ y)
           have i₂ := b0e2362 y
           grind)
        | exact superpose b0e2362 b0e484172
        | (have j1 := b0e2362 y
           grind)
        | exact resolve b0e484172 b0e2362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2362 b0e484172
      have b0e498482 : x = (M.op x x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e498300
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e498300
        | exact resolve b0e498300 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e498300
      have b0e498519 : x = y ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e498482
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e498482
        | exact resolve b0e498482 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e498482
      have b0e498523 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e498519
           have i₂ := b0e482012 y
           grind)
        | exact superpose b0e482012 b0e498519
        | exact resolve b0e498519 b0e482012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e482012 b0e498519
      have b0e498524 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b0e498523
           have r₂ := b0e1564
           grind)
        | exact resolve b0e498523 b0e1564
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e498523
      have b0e500351 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e498524
           grind)
        | exact superpose b0e498524 b0e12
        | exact resolve b0e12 b0e498524
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e498524
      have b0e500385 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e500351
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e500351
        | exact resolve b0e500351 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e500351
      have b0e500386 : x = y := by grind
      clear b0e500385
      have b0e501483 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e1564
           have i₂ := b0e500386
           grind)
        | exact superpose b0e500386 b0e1564
        | exact resolve b0e1564 b0e500386
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1564 b0e500386
      have b0e501718 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e501483
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e501483
        | exact resolve b0e501483 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e501483
      have b0e501767 : False := by grind
      exact b0e501767
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ y) = (k (σ y) (σ y)) := by grind
        have b1e26 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e25
          | exact resolve b1e25 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e31 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : y = (k y y) := by
          first
          | (have i₁ := b1e31
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e31
          | exact resolve b1e31 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e42 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e42 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e42
          | exact resolve b1e42 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e52 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e43 X0
             have i₂ := b1e43 X1
             grind)
          | exact superpose b1e43 b1e43
          | exact resolve b1e43 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e72 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e47 (σ x)
             grind)
          | exact superpose b1e47 b1e19
          | exact resolve b1e19 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e74 : (σ y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e72
             have i₂ := b1e43 x
             grind)
          | exact superpose b1e43 b1e72
          | exact resolve b1e72 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e105 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e32
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e32 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e108 : y = (M.op y y) := by grind
        clear b1e105
        have b1e146 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e108
             have i₂ := b1e52 y X0
             grind)
          | (have i₁ := b1e108
             have i₂ := b1e52 X0 y
             grind)
          | exact superpose b1e52 b1e108
          | exact resolve b1e108 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e108
        have b1e174 : y = (M.op y x) := by
          first
          | (have i₁ := b1e43 x
             have i₂ := b1e146 x
             grind)
          | exact superpose b1e146 b1e43
          | exact resolve b1e43 b1e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e146
        have b1e385 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e74
             have i₂ := b1e174
             grind)
          | exact superpose b1e174 b1e74
          | exact resolve b1e74 b1e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74 b1e174
        have b1e387 : False := by grind
        exact b1e387
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e12 X3 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e84 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e116 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e1332 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e116
        have b2e1347 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1332 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1332
          | exact resolve b2e1332 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1332
        have b2e1550 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e84 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e1551 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1550
             have r₂ := b2e22
             grind)
          | exact resolve b2e1550 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1550
        have b2e1552 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1551
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1551
          | exact resolve b2e1551 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1551
        have b2e1553 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1552
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1552
          | exact resolve b2e1552 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1552
        have b2e1561 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 X0 (σ x) (σ y) x
             have i₂ := b2e1553
             grind)
          | exact superpose b2e1553 b2e34
          | exact resolve b2e34 b2e1553
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e2214 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b2e1347 x
             have i₂ := b2e1561 (σ x) X0
             grind)
          | (have i₁ := b2e1347 x
             have i₂ := b2e1561 X0 (σ x)
             grind)
          | exact superpose b2e1561 b2e1347
          | exact resolve b2e1347 b2e1561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1347 b2e1561
        have b2e3257 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e94 x x
             grind)
          | exact superpose b2e94 b2e21
          | (have j1 := b2e94 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e94 x y
             grind)
          | exact resolve b2e21 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e3402 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e3257
        have b2e20014 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e3402
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e3402
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e3402 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3402
        have b2e20024 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e20014
        have b2e20039 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e20024
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e20024
          | exact resolve b2e20024 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20024
        have b2e20040 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e20039
        have b2e20052 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e20040
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e20040
          | exact resolve b2e20040 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20040
        have b2e20079 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e2214 (σ x)
             have i₂ := b2e20052
             grind)
          | exact superpose b2e20052 b2e2214
          | exact resolve b2e2214 b2e20052
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2214 b2e20052
        have b2e20142 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e20079
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e20079
          | exact resolve b2e20079 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20079
        have b2e22904 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e20142
             grind)
          | exact superpose b2e20142 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e20142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20142
        have b2e22917 : x = (M.op x x) ∨ x = y := by grind
        clear b2e22904
        have b2e22942 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e22917
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e22917
          | exact resolve b2e22917 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22917
        have b2e22943 : x = y := by grind
        clear b2e22942
        have b2e24476 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1553
             have i₂ := b2e22943
             grind)
          | exact superpose b2e22943 b2e1553
          | exact resolve b2e1553 b2e22943
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1553 b2e22943
        have b2e24500 : False := by grind
        exact b2e24500
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e42 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e43 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e43
          | exact resolve b3e43 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b3e131 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e42 (σ x)
             grind)
          | exact superpose b3e42 b3e19
          | exact resolve b3e19 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e136 : (σ y) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e131
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e131
          | exact resolve b3e131 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e131
        have b3e412 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e136
             have i₂ := b3e42 X0
             grind)
          | exact superpose b3e42 b3e136
          | exact resolve b3e136 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e136
        have b3e2817 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e103 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e103
          | exact resolve b3e103 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e3037 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e2817
        have b3e4492 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e3037
             grind)
          | exact superpose b3e3037 b3e13
          | exact resolve b3e13 b3e3037
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4511 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4492
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e4492
          | exact resolve b3e4492 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4492
        have b3e4527 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e4511
             grind)
          | exact superpose b3e4511 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e4511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4511
        have b3e4537 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e4527
        have b3e4547 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e4537
             have r₂ := b3e20
             grind)
          | exact resolve b3e4537 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4537
        have b3e4673 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e4547
        have b3e5241 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e3037
             have i₂ := b3e4673
             grind)
          | exact superpose b3e4673 b3e3037
          | exact resolve b3e3037 b3e4673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3037 b3e4673
        have b3e5256 : (σ x) = (σ y) := by grind
        clear b3e5241
        have b3e5437 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e5256
             grind)
          | exact superpose b3e5256 b3e22
          | exact resolve b3e22 b3e5256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5256
        have b3e5465 : False := by grind
        exact b3e5465
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e45 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e45
            | exact resolve b4e45 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e50 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e44 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e44
            | exact resolve b4e44 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e76 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e50 (σ x)
               grind)
            | exact superpose b4e50 b4e20
            | exact resolve b4e20 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e78 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e76
               have i₂ := b4e49 x
               grind)
            | exact superpose b4e49 b4e76
            | exact resolve b4e76 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e76
          have b4e79 : False := by grind
          exact b4e79
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b5e39 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e39 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e39
            | exact resolve b5e39 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e59 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e46 y
               grind)
            | exact superpose b5e46 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e46 y
               grind)
            | exact resolve b5e17 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e60 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e59 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e87 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e98 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e103 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e98 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e349 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            grind
          clear b5e60
          have b5e368 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e349 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e349
          have b5e437 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e368 (τ X0)
               grind)
            | exact superpose b5e368 b5e27
            | exact resolve b5e27 b5e368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e368
          have b5e438 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e437 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e437
            | exact resolve b5e437 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e437
          have b5e996 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X1 X0) X1) ∨ (k (M.op X0 X1) (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 X1) X0 X1
               have i₂ := b5e103 (M.op X0 X1)
               grind)
            | exact superpose b5e103 b5e13
            | (have j1 := b5e103 (M.op X0 X1)
               grind)
            | exact resolve b5e13 b5e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1019 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e996 X0 X1
               have i₂ := b5e438 (M.op X0 X1)
               grind)
            | exact superpose b5e438 b5e996
            | (have j0 := b5e996 X0 X1
               grind)
            | exact resolve b5e996 b5e438
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e996
          have b5e1416 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e20
               have i₂ := b5e87 (σ y) (σ x) X0
               grind)
            | (have i₁ := b5e20
               have i₂ := b5e87 (σ x) x (σ y)
               grind)
            | exact superpose b5e87 b5e20
            | (have j1 := b5e87 (σ y) x X0
               grind)
            | exact resolve b5e20 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e1543 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e1416 X0
               grind)
            | (have r₁ := b5e1416 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e1416 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1416
          have b5e1572 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e1543 X0
               have i₂ := b5e46 x
               grind)
            | exact superpose b5e46 b5e1543
            | (have j0 := b5e1543 X0
               grind)
            | exact resolve b5e1543 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e1543
          have b5e1576 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1572 X0
               have i₂ := b5e438 X0
               grind)
            | exact superpose b5e438 b5e1572
            | (have j0 := b5e1572 X0
               grind)
            | exact resolve b5e1572 b5e438
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1572
          have b5e5619 : ∀ X0 X1 : G, (σ y) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1576 (M.op X1 X0)
               have i₂ := b5e13 (σ y) X1 X0
               grind)
            | exact superpose b5e13 b5e1576
            | (have j0 := b5e1576 (M.op X1 X0)
               grind)
            | exact resolve b5e1576 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1576
          have b5e5636 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e5619 X0 X1
               have j1 := b5e1019 X1 X0
               grind)
            | (have r₁ := b5e5619 X1 X0
               have r₂ := b5e1019 X0 X1
               grind)
            | exact resolve b5e5619 b5e1019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1019 b5e5619
          have b5e6069 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e5636 X0 X0
               have i₂ := b5e103 X0
               grind)
            | exact superpose b5e103 b5e5636
            | (have j1 := b5e103 (σ y)
               grind)
            | exact resolve b5e5636 b5e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103 b5e5636
          have b5e6187 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e6069 X0
               grind)
            | (have r₁ := b5e6069 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e6069 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6069
          have b5e6196 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e6187 X0
               have i₂ := b5e438 X0
               grind)
            | exact superpose b5e438 b5e6187
            | exact resolve b5e6187 b5e438
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e438 b5e6187
          have b5e6407 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e6196 (σ y)
               grind)
            | exact superpose b5e6196 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e6196 (σ y)
               grind)
            | exact resolve b5e24 b5e6196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6196
          have b5e6414 : False := by grind
          exact b5e6414
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ x) = (σ (k x y)) := by
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
        have b6e44 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e44 X0
             have i₂ := b6e44 X1
             grind)
          | exact superpose b6e44 b6e44
          | exact resolve b6e44 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b6e99 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e25
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e25 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e101 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e99
             have r₂ := b6e20
             grind)
          | exact resolve b6e99 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e104 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e101
             have r₂ := b6e21
             grind)
          | exact resolve b6e101 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e101
        have b6e854 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e63 (σ x) X0
             grind)
          | (have i₁ := b6e19
             have i₂ := b6e63 X0 (σ x)
             grind)
          | exact superpose b6e63 b6e19
          | exact resolve b6e19 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e855 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e854 X0
             have i₂ := b6e104
             grind)
          | exact superpose b6e104 b6e854
          | exact resolve b6e854 b6e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104 b6e854
        have b6e871 : (σ x) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e855 x
             have i₂ := b6e44 x
             grind)
          | exact superpose b6e44 b6e855
          | exact resolve b6e855 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e855
        have b6e2727 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e96 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e96
          | exact resolve b6e96 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e2930 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e2727
        have b6e4353 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e2930
             grind)
          | exact superpose b6e2930 b6e13
          | exact resolve b6e13 b6e2930
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4369 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4353
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e4353
          | exact resolve b6e4353 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4353
        have b6e5040 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e4369
             grind)
          | exact superpose b6e4369 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e4369
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4369
        have b6e5050 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e5040
        have b6e5058 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e5050
             have r₂ := b6e20
             grind)
          | exact resolve b6e5050 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5050
        have b6e5272 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e5058
        have b6e6034 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2930
             have i₂ := b6e5272
             grind)
          | exact superpose b6e5272 b6e2930
          | exact resolve b6e2930 b6e5272
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2930 b6e5272
        have b6e6049 : (σ x) = (σ y) := by grind
        clear b6e6034
        have b6e6133 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e6049
             grind)
          | exact superpose b6e6049 b6e22
          | exact resolve b6e22 b6e6049
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e6142 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e871
             have i₂ := b6e6049
             grind)
          | exact superpose b6e6049 b6e871
          | exact resolve b6e871 b6e6049
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e871 b6e6049
        have b6e6165 : False := by grind
        exact b6e6165
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ y) = (k (σ y) (σ y)) := by grind
          have b7e27 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e26
            | exact resolve b7e26 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e32 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e27
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : y = (k y y) := by
            first
            | (have i₁ := b7e32
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e32
            | exact resolve b7e32 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e89 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e18 y y
               grind)
            | exact superpose b7e18 b7e33
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e33 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e92 : y = (M.op y y) := by grind
          clear b7e89
          have b7e96 : False := by grind
          exact b7e96
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1221 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e1222 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1221
               have r₂ := b8e24
               grind)
            | exact resolve b8e1221 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1221
          have b8e1223 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1222
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1222
            | exact resolve b8e1222 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1222
          have b8e1224 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1223
               grind)
            | exact superpose b8e1223 b8e20
            | exact resolve b8e20 b8e1223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1223
          have b8e1246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1224
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1224
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1224 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1224
          have b8e1247 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e1246
          have b8e1250 : y = (M.op y y) := by
            first
            | (have r₁ := b8e1247
               have r₂ := b8e21
               grind)
            | exact resolve b8e1247 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1247
          have b8e1253 : False := by grind
          exact b8e1253

/-- `Equation4559`: `x ◇ (y ◇ z) = (w ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pxy_Equation4559 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4559 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4559.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
        intro X0 X1 X2 X3
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e34 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) X0 X1 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2 x
           have i₂ := b0e11 X0 X3 X2 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : (M.op y (σ x)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b0e40 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e40
        | exact resolve b0e40 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e40 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e40
        | exact resolve b0e40 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op x (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 x (M.op X1 X0)
           have i₂ := b0e40 X1 X0
           grind)
        | exact superpose b0e40 b0e40
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 X3)) = (M.op (M.op y X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X1 X0) X2 X3 x
           have i₂ := b0e40 X1 X0
           grind)
        | exact superpose b0e40 b0e11
        | exact resolve b0e11 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e49 X0 X1
           have i₂ := b0e40 y X0
           grind)
        | exact superpose b0e40 b0e49
        | exact resolve b0e49 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e57 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X3 X0) ∨ (M.op X3 X0) = (M.op X2 X2) ∨ (M.op X2 X2) = (k X2 (M.op X3 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e15 X2 (M.op X3 X0)
           have i₂ := b0e11 X0 X1 X2 X3
           grind)
        | exact superpose b0e11 b0e15
        | (have j0 := b0e15 X2 (M.op X3 X0)
           grind)
        | (have r₁ := b0e15 X2 (M.op (M.op X1 X2) (M.op X1 X2))
           have r₂ := b0e11 (M.op X1 X2) X1 X2 (M.op X1 X2)
           grind)
        | exact resolve b0e15 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e40 y x
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e40
        | exact resolve b0e40 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 X1 y
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e11
        | exact resolve b0e11 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e68 : ∀ X1 : G, (M.op y X1) = (M.op (M.op x y) X1) := by
        intro X1
        first
        | (have i₁ := b0e67 x X1
           have i₂ := b0e40 x X1
           grind)
        | exact superpose b0e40 b0e67
        | exact resolve b0e67 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e69 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e66
           have i₂ := b0e40 x y
           grind)
        | exact superpose b0e40 b0e66
        | exact resolve b0e66 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e66
      have b0e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e82 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X0 X3) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X3 X1
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X0 (M.op X3 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e87 : (M.op x y) = (k y (M.op x y)) := by grind
      have b0e98 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e26 X1 X0
           grind)
        | exact superpose b0e26 b0e12
        | exact resolve b0e12 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e112 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : (M.op (σ x) (σ y)) = (M.op (M.op x (σ y)) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ x) y
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e34
        | exact resolve b0e34 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e128 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e117
           have i₂ := b0e34 (σ y) x
           grind)
        | exact superpose b0e34 b0e117
        | exact resolve b0e117 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e287 : ∀ X0 X1 : G, (M.op (σ x) (M.op y X0)) = (M.op (σ y) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 y (M.op X1 X0)
           have i₂ := b0e53 X0 X1
           grind)
        | exact superpose b0e53 b0e39
        | exact resolve b0e39 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e308 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e287 X0 X1
           have i₂ := b0e39 y X0
           grind)
        | exact superpose b0e39 b0e287
        | exact resolve b0e287 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e287
      have b0e380 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X0 X1 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e41
        | exact resolve b0e41 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e511 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X2 X0) x) := by
        intro X0 X2
        first
        | (have i₁ := b0e11 X0 x x X2
           have i₂ := b0e380 X0 x
           grind)
        | exact superpose b0e380 b0e11
        | exact resolve b0e11 b0e380
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e380
      have b0e847 : (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) := by grind
      clear b0e68
      have b0e872 : (M.op y y) = (k (M.op x y) (M.op y y)) := by
        first
        | (have i₁ := b0e847
           have i₂ := b0e53 y x
           grind)
        | exact superpose b0e53 b0e847
        | exact resolve b0e847 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53 b0e847
      have b0e880 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e872
           have i₂ := b0e69
           grind)
        | exact superpose b0e69 b0e872
        | exact resolve b0e872 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69 b0e872
      have b0e2850 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e79 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e3931 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e82 X0 X1 X2 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82
      have b0e4692 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have j0 := b0e57 X1 X1 (M.op X0 X1) X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e4693 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X1) X1) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e4692 X0 X1
           have i₂ := b0e52 X1 X0 X0 X1
           grind)
        | exact superpose b0e52 b0e4692
        | (have j0 := b0e4692 X0 X1
           grind)
        | exact resolve b0e4692 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4692
      have b0e4755 : ∀ X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op y X1) X1)) ∨ (M.op X1 X1) = (M.op (M.op y X1) X1) := by
        intro X1
        first
        | (have i₁ := b0e4693 x X1
           have i₂ := b0e52 X1 x x X1
           grind)
        | exact superpose b0e52 b0e4693
        | (have j0 := b0e4693 x X1
           grind)
        | exact resolve b0e4693 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52 b0e4693
      have b0e5376 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e76 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e5377 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e5376 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5376
      have b0e19709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e5377 (M.op x y)
           have i₂ := b0e880
           grind)
        | exact superpose b0e880 b0e5377
        | (have j0 := b0e5377 (M.op x y)
           grind)
        | exact resolve b0e5377 b0e880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e880 b0e5377
      have b0e19718 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e19709
      have b0e19940 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ (M.op x y)) (σ (M.op x y))
           have i₂ := b0e19718
           grind)
        | exact superpose b0e19718 b0e34
        | exact resolve b0e34 b0e19718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e19948 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e39 (σ (M.op x y)) (σ (M.op x y))
           have i₂ := b0e19718
           grind)
        | exact superpose b0e19718 b0e39
        | exact resolve b0e39 b0e19718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e19718
      have b0e24304 : ∀ X1 : G, (M.op (σ y) (σ y)) ≠ X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
        intro X1
        first
        | (have i₁ := b0e3931 X1 (σ y) x
           have i₂ := b0e308 (σ y) x
           grind)
        | exact superpose b0e308 b0e3931
        | (have j0 := b0e3931 X1 (σ y) x
           grind)
        | (have r₁ := b0e3931 (M.op (σ y) (M.op X1 (M.op x (σ y)))) (σ y) x
           have r₂ := b0e308 (M.op x (σ y)) X1
           grind)
        | (have r₁ := b0e3931 (M.op (σ y) (σ y)) (σ y) X1
           have r₂ := b0e308 (σ y) X1
           grind)
        | exact resolve b0e3931 b0e308
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e308 b0e3931
      have b0e24312 : ∀ X1 : G, (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
        intro X1
        first
        | (have j0 := b0e24304 X1
           have j1 := b0e16 (σ y) X1
           grind)
        | (have r₁ := b0e24304 (k (σ y) (σ y))
           have r₂ := b0e16 (σ y) (σ y)
           grind)
        | (have r₁ := b0e24304 X1
           have r₂ := b0e16 (σ y) X1
           grind)
        | (have r₁ := b0e24304 (M.op x x)
           have r₂ := b0e16 x (M.op (σ y) (σ y))
           grind)
        | exact resolve b0e24304 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24304
      have b0e24758 : (M.op x x) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e4755 x
           have i₂ := b0e511 x y
           grind)
        | exact superpose b0e511 b0e4755
        | exact resolve b0e4755 b0e511
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e511 b0e4755
      have b0e24845 : y = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e24758
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e24758
        | exact resolve b0e24758 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24758
      have b0e24874 : y = (k x (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e24845
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e24845
        | exact resolve b0e24845 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24845
      have b0e30396 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e98 y X0
           have i₂ := b0e24312 X0
           grind)
        | exact superpose b0e24312 b0e98
        | (have j1 := b0e24312 X0
           grind)
        | exact resolve b0e98 b0e24312
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98 b0e24312
      have b0e32271 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e15 (σ y) (σ (M.op x y))
           have i₂ := b0e19940
           grind)
        | exact superpose b0e19940 b0e15
        | (have j0 := b0e15 (σ y) (σ (M.op x y))
           grind)
        | exact resolve b0e15 b0e19940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e32271
           have i₂ := b0e128
           grind)
        | exact superpose b0e128 b0e32271
        | exact resolve b0e32271 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32271
      have b0e32445 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
        first
        | (have r₁ := b0e32398
           have r₂ := b0e18
           grind)
        | exact resolve b0e32398 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32398
      have b0e32454 : (M.op (σ y) (σ y)) = (σ (k y (M.op x y))) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e32445
           have i₂ := b0e17 y (M.op x y)
           grind)
        | exact superpose b0e17 b0e32445
        | exact resolve b0e32445 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32445
      have b0e32455 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e32454
           have i₂ := b0e87
           grind)
        | exact superpose b0e87 b0e32454
        | exact resolve b0e32454 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32454
      have b0e32456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e32455
           have i₂ := b0e128
           grind)
        | exact superpose b0e128 b0e32455
        | exact resolve b0e32455 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128 b0e32455
      have b0e32457 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have r₁ := b0e32456
           have r₂ := b0e18
           grind)
        | exact resolve b0e32456 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32456
      have b0e63037 : (k y (τ (σ (M.op x y)))) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
        first
        | (have i₁ := b0e30396 (σ (M.op x y))
           have i₂ := b0e19948
           grind)
        | exact superpose b0e19948 b0e30396
        | (have j0 := b0e30396 (σ (M.op x y))
           grind)
        | exact resolve b0e30396 b0e19948
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19948 b0e30396
      have b0e63160 : (k y (M.op x y)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
        first
        | (have i₁ := b0e63037
           have i₂ := b0e12 (M.op x y)
           grind)
        | exact superpose b0e12 b0e63037
        | exact resolve b0e63037 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63037
      have b0e63194 : (M.op x y) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
        first
        | (have i₁ := b0e63160
           have i₂ := b0e87
           grind)
        | exact superpose b0e87 b0e63160
        | exact resolve b0e63160 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87 b0e63160
      have b0e63212 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ (M.op x y)))) := by
        first
        | (have i₁ := b0e63194
           have i₂ := b0e19940
           grind)
        | exact superpose b0e19940 b0e63194
        | exact resolve b0e63194 b0e19940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19940 b0e63194
      have b0e63216 : (M.op x y) = (τ (M.op (σ x) (σ (M.op x y)))) := by
        first
        | (have r₁ := b0e63212
           have r₂ := b0e32457
           grind)
        | exact resolve b0e63212 b0e32457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63212
      have b0e63278 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e13 (M.op (σ x) (σ (M.op x y)))
           have i₂ := b0e63216
           grind)
        | exact superpose b0e63216 b0e13
        | exact resolve b0e13 b0e63216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63216
      have b0e63505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e2850 (σ x) (σ (M.op x y))
           have i₂ := b0e63278
           grind)
        | exact superpose b0e63278 b0e2850
        | (have j0 := b0e2850 (σ x) (σ (M.op x y))
           grind)
        | (have r₁ := b0e2850 (σ x) (σ (M.op x y))
           have r₂ := b0e63278
           grind)
        | exact resolve b0e2850 b0e63278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2850
      have b0e63525 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by grind
      clear b0e63505
      have b0e63530 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
        first
        | (have r₁ := b0e63525
           have r₂ := b0e32457
           grind)
        | exact resolve b0e63525 b0e32457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63525
      have b0e63542 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
        first
        | (have i₁ := b0e63530
           have i₂ := b0e17 x (M.op x y)
           grind)
        | exact superpose b0e17 b0e63530
        | exact resolve b0e63530 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63530
      have b0e63790 : (τ (σ (M.op x y))) = (k x (M.op x y)) := by
        first
        | (have i₁ := b0e12 (k x (M.op x y))
           have i₂ := b0e63542
           grind)
        | exact superpose b0e63542 b0e12
        | exact resolve b0e12 b0e63542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63542
      have b0e63844 : (M.op x y) = (k x (M.op x y)) := by
        first
        | (have i₁ := b0e63790
           have i₂ := b0e12 (M.op x y)
           grind)
        | exact superpose b0e12 b0e63790
        | exact resolve b0e63790 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63790
      have b0e64613 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e24874
           have i₂ := b0e63844
           grind)
        | exact superpose b0e63844 b0e24874
        | exact resolve b0e24874 b0e63844
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24874 b0e63844
      have b0e64625 : y = (M.op x y) := by grind
      clear b0e64613
      have b0e64897 : (σ y) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e32457
           have i₂ := b0e64625
           grind)
        | exact superpose b0e64625 b0e32457
        | exact resolve b0e32457 b0e64625
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32457
      have b0e64899 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e63278
           have i₂ := b0e64625
           grind)
        | exact superpose b0e64625 b0e63278
        | exact resolve b0e63278 b0e64625
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63278 b0e64625
      have b0e65013 : (σ y) ≠ (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e64897
           have i₂ := b0e112
           grind)
        | exact superpose b0e112 b0e64897
        | exact resolve b0e64897 b0e112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112 b0e64897
      have b0e65019 : False := by grind
      exact b0e65019
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y = (k x y) := by grind
        have b1e53 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e56 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e53
        have b1e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e56
             have r₂ := b1e21
             grind)
          | exact resolve b1e56 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e61 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e63 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e61
          | exact resolve b1e61 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e61
        have b1e64 : False := by grind
        exact b1e64
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3192 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e75 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e3193 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e3192
             have r₂ := b2e22
             grind)
          | exact resolve b2e3192 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3192
        have b2e3194 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e3193
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e3193
          | exact resolve b2e3193 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3193
        have b2e3195 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e3194
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e3194
          | exact resolve b2e3194 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e3194
        have b2e4604 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e67 x x
             grind)
          | exact superpose b2e67 b2e21
          | (have j1 := b2e67 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e67 x y
             grind)
          | exact resolve b2e21 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e4724 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e4604
        have b2e15892 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e4724
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e4724
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e4724 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4724
        have b2e15893 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e15892
        have b2e15894 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15893
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15893
          | exact resolve b2e15893 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15893
        have b2e15895 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e15894
        have b2e15901 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e15895
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15895
          | exact resolve b2e15895 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15895
        have b2e15910 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e15901
             grind)
          | exact superpose b2e15901 b2e21
          | exact resolve b2e21 b2e15901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e15913 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
        clear b2e15901
        have b2e15962 : (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e15913
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e15913
          | exact resolve b2e15913 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15913
        have b2e17051 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15962
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e15962
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e15962 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15962
        have b2e17073 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
        clear b2e17051
        have b2e17087 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17073
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17073
          | exact resolve b2e17073 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17073
        have b2e17091 : x = y ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e17087
             have r₂ := b2e15910
             grind)
          | exact resolve b2e17087 b2e15910
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15910 b2e17087
        have b2e17095 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e17091
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17091
          | exact resolve b2e17091 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17091
        have b2e17096 : x = y := by grind
        clear b2e17095
        have b2e17205 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e17096
             grind)
          | exact superpose b2e17096 b2e22
          | exact resolve b2e22 b2e17096
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e17222 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e3195
             have i₂ := b2e17096
             grind)
          | exact superpose b2e17096 b2e3195
          | exact resolve b2e3195 b2e17096
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3195 b2e17096
        have b2e17232 : False := by grind
        exact b2e17232
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
        have b3e67 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e68 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e67
        have b3e69 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e68
             have r₂ := b3e20
             grind)
          | exact resolve b3e68 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e72 : y = (M.op x x) := by
          first
          | (have i₁ := b3e69
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e69
          | exact resolve b3e69 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e69
        have b3e75 : False := by grind
        exact b3e75
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : y = (M.op x y) := by
            first
            | (have i₁ := b4e36 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e155 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e30 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e30
            | exact resolve b4e30 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e179 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e155
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e155
            | exact resolve b4e155 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155
          have b4e273 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e179
               grind)
            | exact superpose b4e179 b4e20
            | exact resolve b4e20 b4e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e179
          have b4e283 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e273
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e273
            | exact resolve b4e273 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e273
          have b4e284 : False := by grind
          exact b4e284
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
            intro X0 X1 X2 X3
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e32 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 X1 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X2 x
               have i₂ := b5e13 X0 X3 X2 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op x (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 x (M.op X1 X0)
               have i₂ := b5e32 X1 X0
               grind)
            | exact superpose b5e32 b5e32
            | exact resolve b5e32 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : y = (M.op x y) := by
            first
            | (have i₁ := b5e32 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X0 X1
               have i₂ := b5e32 y X0
               grind)
            | exact superpose b5e32 b5e41
            | exact resolve b5e41 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e52 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b5e53 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b5e52
          have b5e54 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e21
               grind)
            | exact resolve b5e53 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e60 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e32 x y
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e32
            | exact resolve b5e32 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e62 : y = (M.op y y) := by
            first
            | (have i₁ := b5e60
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e60
            | exact resolve b5e60 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e71 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X0 X3) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3 X1
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2 X3
               have i₂ := b5e18 X0 (M.op X3 X0)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 X1 X2 X3 : G, (k (M.op X3 X1) X0) = (M.op (M.op X3 X1) X0) ∨ (M.op X1 (M.op X2 (M.op X3 X1))) = X0 ∨ (M.op X0 (M.op X3 X1)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 (M.op X3 X1) X3
               have i₂ := b5e18 (M.op X3 X1) X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2 X3
               have i₂ := b5e18 X0 (M.op (M.op X3 X0) X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 (M.op X3 X1) X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e76 : y = (k y y) := by grind
          have b5e245 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e35 X1 X2 (M.op X3 X0) y
               have i₂ := b5e46 X0 X3
               grind)
            | exact superpose b5e46 b5e35
            | exact resolve b5e35 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e3042 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e75 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e3043 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e3042
               have r₂ := b5e24
               grind)
            | exact resolve b5e3042 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3042
          have b5e3044 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e3043
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e3043
            | exact resolve b5e3043 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3043
          have b5e3045 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e3044
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e3044
            | exact resolve b5e3044 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e3044
          have b5e3048 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ (M.op x x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ y) X0 X1 (σ x)
               have i₂ := b5e3045
               grind)
            | exact superpose b5e3045 b5e13
            | exact resolve b5e13 b5e3045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3062 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x x))) = (M.op X0 (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X0 X1 (σ y) (σ x)
               have i₂ := b5e3045
               grind)
            | exact superpose b5e3045 b5e35
            | exact resolve b5e35 b5e3045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3295 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e71 X0 X1 X2 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e4771 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e67 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e4772 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e4771 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4771
          have b5e5103 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e73 X0 y x y
               have i₂ := b5e62
               grind)
            | exact superpose b5e62 b5e73
            | exact resolve b5e73 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e5320 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
            intro X1
            first
            | (have j0 := b5e5103 x X1
               have j1 := b5e3295 X1 y x
               grind)
            | (have r₁ := b5e5103 x x
               have r₂ := b5e3295 x y x
               grind)
            | (have r₁ := b5e5103 x (M.op X1 (M.op x X1))
               have r₂ := b5e3295 (M.op y (M.op x y)) X1 x
               grind)
            | (have r₁ := b5e5103 x (M.op x y)
               have r₂ := b5e3295 (k y (M.op x y)) y x
               grind)
            | exact resolve b5e5103 b5e3295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5103
          have b5e6443 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e5320 (τ X0)
               grind)
            | exact superpose b5e5320 b5e27
            | (have j1 := b5e5320 (τ X0)
               grind)
            | exact resolve b5e27 b5e5320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e5320
          have b5e13867 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ y) (M.op X0 (M.op X1 (σ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3048 X0 (M.op X1 (σ y))
               have i₂ := b5e3062 (σ (M.op x x)) X1
               grind)
            | exact superpose b5e3062 b5e3048
            | exact resolve b5e3048 b5e3062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3048 b5e3062
          have b5e14016 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ y) (M.op y (σ y))) := by
            first
            | (have i₁ := b5e13867 x x
               have i₂ := b5e245 (σ y) (σ y) x x
               grind)
            | exact superpose b5e245 b5e13867
            | exact resolve b5e13867 b5e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e245 b5e13867
          have b5e15353 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e4772 y
               have i₂ := b5e76
               grind)
            | exact superpose b5e76 b5e4772
            | (have j0 := b5e4772 y
               grind)
            | exact resolve b5e4772 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76 b5e4772
          have b5e15358 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e15353
          have b5e15403 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X0 X1 (σ y) (σ y)
               have i₂ := b5e15358
               grind)
            | exact superpose b5e15358 b5e35
            | exact resolve b5e35 b5e15358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e15415 : ∀ X0 X1 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ y) (M.op X1 (σ y))) = X0 ∨ (M.op X0 (σ y)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e73 X0 (σ y) x (σ y)
               have i₂ := b5e15358
               grind)
            | exact superpose b5e15358 b5e73
            | exact resolve b5e73 b5e15358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e15445 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b5e15415 X0 x
               have j1 := b5e3295 X0 (σ y) x
               grind)
            | (have r₁ := b5e15415 (M.op x (σ y)) x
               have r₂ := b5e3295 (k (σ y) (M.op x (σ y))) (σ y) x
               grind)
            | (have r₁ := b5e15415 X0 x
               have r₂ := b5e3295 X0 (σ y) x
               grind)
            | (have r₁ := b5e15415 (M.op x (M.op x x)) x
               have r₂ := b5e3295 (M.op (σ y) (M.op x (σ y))) x x
               grind)
            | exact resolve b5e15415 b5e3295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3295 b5e15415
          have b5e84661 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e19 y X0
               have i₂ := b5e15445 (σ X0)
               grind)
            | exact superpose b5e15445 b5e19
            | (have j1 := b5e15445 (σ X0)
               grind)
            | exact resolve b5e19 b5e15445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15445
          have b5e185487 : ∀ X0 : G, (σ (M.op y X0)) = (k (σ y) (σ X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e6443 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e6443
            | exact resolve b5e6443 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6443
          have b5e185541 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e185487 X0
               have i₂ := b5e19 y X0
               grind)
            | exact superpose b5e19 b5e185487
            | (have j0 := b5e185487 X0
               grind)
            | exact resolve b5e185487 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e185487
          have b5e297798 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e84661 x
               grind)
            | exact superpose b5e84661 b5e24
            | (have j1 := b5e84661 x
               grind)
            | exact resolve b5e24 b5e84661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84661
          have b5e298193 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e297798
               have i₂ := b5e3045
               grind)
            | exact superpose b5e3045 b5e297798
            | exact resolve b5e297798 b5e3045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3045 b5e297798
          have b5e300701 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e298193
               have i₂ := b5e185541 x
               grind)
            | exact superpose b5e185541 b5e298193
            | (have j1 := b5e185541 x
               grind)
            | exact resolve b5e298193 b5e185541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e185541 b5e298193
          have b5e300702 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e300701
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e300701
            | exact resolve b5e300701 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e300701
          have b5e300703 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
          clear b5e300702
          have b5e300714 : (σ x) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b5e300703
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e300703
            | exact resolve b5e300703 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e300703
          have b5e303158 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op y (σ y))) ∨ x = y := by
            first
            | (have i₁ := b5e14016
               have i₂ := b5e300714
               grind)
            | exact superpose b5e300714 b5e14016
            | exact resolve b5e14016 b5e300714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14016 b5e300714
          have b5e303286 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e303158
               have i₂ := b5e15403 (σ y) y
               grind)
            | exact superpose b5e15403 b5e303158
            | exact resolve b5e303158 b5e15403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15403 b5e303158
          have b5e303311 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e303286
               have i₂ := b5e15358
               grind)
            | exact superpose b5e15358 b5e303286
            | exact resolve b5e303286 b5e15358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e303286
          have b5e303317 : x = y := by
            first
            | (have r₁ := b5e303311
               have r₂ := b5e23
               grind)
            | exact resolve b5e303311 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e303311
          have b5e306397 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e303317
               grind)
            | exact superpose b5e303317 b5e24
            | exact resolve b5e24 b5e303317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e306470 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e15358
               have i₂ := b5e303317
               grind)
            | exact superpose b5e303317 b5e15358
            | exact resolve b5e15358 b5e303317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15358 b5e303317
          have b5e306582 : False := by grind
          exact b5e306582
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
        have b6e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e83 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e25
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e25 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e91 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e20
             grind)
          | exact resolve b6e83 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e94 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b6e91
             have r₂ := b6e21
             grind)
          | exact resolve b6e91 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91
        have b6e4374 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e80 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e80
          | exact resolve b6e80 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e4520 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e4374
        have b6e5424 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e4520
             grind)
          | exact superpose b6e4520 b6e13
          | exact resolve b6e13 b6e4520
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5442 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e5424
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e5424
          | exact resolve b6e5424 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5424
        have b6e6026 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e5442
             grind)
          | exact superpose b6e5442 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e5442
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5442
        have b6e6027 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e6026
        have b6e6029 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e6027
             have r₂ := b6e20
             grind)
          | exact resolve b6e6027 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6027
        have b6e6345 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e6029
        have b6e7923 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4520
             have i₂ := b6e6345
             grind)
          | exact superpose b6e6345 b6e4520
          | exact resolve b6e4520 b6e6345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4520 b6e6345
        have b6e7930 : (σ x) = (σ y) := by grind
        clear b6e7923
        have b6e8711 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e7930
             grind)
          | exact superpose b6e7930 b6e19
          | exact resolve b6e19 b6e7930
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7930
        have b6e8734 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e8711
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e8711
          | exact resolve b6e8711 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8711
        have b6e8738 : False := by grind
        exact b6e8738
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) X0 X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (k (M.op X1 X2) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
            intro X0 X1 X2
            grind
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e48 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e49
            | exact resolve b7e49 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e18 (σ X0) (σ X1)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e74 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e23
            | exact resolve b7e23 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ (k x y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) X0 X1 (σ x)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e13
            | exact resolve b7e13 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e79 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ (k x y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ x) (σ x) X1
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e13
            | exact resolve b7e13 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e80 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e79 X0 x
               have i₂ := b7e28 X0 x
               grind)
            | exact superpose b7e28 b7e79
            | exact resolve b7e79 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e81 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (k x y)) X1) := by
            intro X1
            first
            | (have i₁ := b7e78 x X1
               have i₂ := b7e33 x X1
               grind)
            | exact superpose b7e33 b7e78
            | exact resolve b7e78 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e78
          have b7e83 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e28 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e28
            | exact resolve b7e28 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = (M.op (M.op X0 (M.op X1 X2)) (σ x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e28 X2 (M.op x X0)
               have i₂ := b7e13 X0 X1 X2 x
               grind)
            | exact superpose b7e13 b7e28
            | exact resolve b7e28 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e88 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e28 (σ x) (M.op x X0)
               have i₂ := b7e28 X0 x
               grind)
            | exact superpose b7e28 b7e28
            | exact resolve b7e28 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e97 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e88 x
               have i₂ := b7e28 (σ y) x
               grind)
            | exact superpose b7e28 b7e88
            | exact resolve b7e88 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e98 : ∀ X1 X2 : G, (M.op X2 (σ y)) = (M.op (M.op X1 X2) (σ y)) := by
            intro X1 X2
            first
            | (have i₁ := b7e87 x X1 X2
               have i₂ := b7e28 (M.op X1 X2) x
               grind)
            | exact superpose b7e28 b7e87
            | exact resolve b7e87 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e101 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e83
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e83
            | exact resolve b7e83 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e873 : (M.op (σ (k x y)) (σ y)) = (k (σ (k x y)) (M.op (σ (k x y)) (σ y))) := by grind
          clear b7e80
          have b7e917 : (M.op (σ y) (σ y)) = (k (σ (k x y)) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e873
               have i₂ := b7e81 (σ y)
               grind)
            | exact superpose b7e81 b7e873
            | exact resolve b7e873 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e873
          have b7e930 : (M.op (σ x) (σ y)) = (k (σ (k x y)) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e917
               have i₂ := b7e97
               grind)
            | exact superpose b7e97 b7e917
            | exact resolve b7e917 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e917
          have b7e941 : (σ y) = (k (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b7e930
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e930
            | exact resolve b7e930 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e930
          have b7e945 : (σ y) = (σ (k (k x y) y)) := by
            first
            | (have i₁ := b7e941
               have i₂ := b7e19 (k x y) y
               grind)
            | exact superpose b7e19 b7e941
            | exact resolve b7e941 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e941
          have b7e1256 : (σ y) = (σ (k (M.op x y) y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e945
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e945
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e945 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1267 : (σ y) = (σ (k (M.op x y) y)) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e1256
               have r₂ := b7e21
               grind)
            | exact resolve b7e1256 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1256
          have b7e1268 : (σ y) = (σ (k (M.op x y) y)) := by
            first
            | (have r₁ := b7e1267
               have r₂ := b7e22
               grind)
            | exact resolve b7e1267 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1267
          have b7e1676 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (k (M.op X0 (σ x)) (M.op (M.op X0 (σ x)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e38 x x (σ x)
               have i₂ := b7e28 (M.op x (σ x)) x
               grind)
            | exact superpose b7e28 b7e38
            | exact resolve b7e38 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e38
          have b7e1697 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e1676 X0
               have i₂ := b7e98 x (M.op X0 (σ x))
               grind)
            | (have i₁ := b7e1676 x
               have i₂ := b7e98 x (σ x)
               grind)
            | exact superpose b7e98 b7e1676
            | exact resolve b7e1676 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e1676
          have b7e1720 : ∀ X0 : G, (σ y) = (k (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e1697 X0
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e1697
            | exact resolve b7e1697 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101 b7e1697
          have b7e1854 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e1720 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1720
            | exact resolve b7e1720 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1720
          have b7e1874 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e1854
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e1854
            | exact resolve b7e1854 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1854
          have b7e1884 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1874
               grind)
            | exact superpose b7e1874 b7e14
            | exact resolve b7e14 b7e1874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1874
          have b7e1886 : y = (k y y) := by
            first
            | (have i₁ := b7e1884
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1884
            | exact resolve b7e1884 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1884
          have b7e2125 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e1886
               grind)
            | exact superpose b7e1886 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e1886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1886
          have b7e2126 : y = (M.op y y) := by grind
          clear b7e2125
          have b7e2375 : ∀ X0 X1 : G, (M.op y X1) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 y X0 X1 y
               have i₂ := b7e2126
               grind)
            | exact superpose b7e2126 b7e13
            | exact resolve b7e13 b7e2126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2627 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e64 x x
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e64
            | exact resolve b7e64 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50 b7e64
          have b7e2757 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by grind
          clear b7e2627
          have b7e19920 : (k x y) = (τ (σ (k x x))) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e2757
               grind)
            | exact superpose b7e2757 b7e14
            | exact resolve b7e14 b7e2757
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2757
          have b7e19951 : (σ x) = (σ (k x y)) ∨ (k x y) = (k x x) := by
            first
            | (have i₁ := b7e19920
               have i₂ := b7e14 (k x x)
               grind)
            | exact superpose b7e14 b7e19920
            | exact resolve b7e19920 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19920
          have b7e21658 : (k x y) = (τ (σ x)) ∨ (k x y) = (k x x) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e19951
               grind)
            | exact superpose b7e19951 b7e14
            | exact resolve b7e14 b7e19951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19951
          have b7e21691 : (k x y) = (k x x) ∨ x = (k x y) := by
            first
            | (have i₁ := b7e21658
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e21658
            | exact resolve b7e21658 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21658
          have b7e24685 : (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ x = (k x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e21691
               grind)
            | exact superpose b7e21691 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e21691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21691
          have b7e24687 : (M.op x y) = (k x x) ∨ y = (M.op y x) ∨ x = (k x y) := by
            first
            | (have r₁ := b7e24685
               have r₂ := b7e21
               grind)
            | exact resolve b7e24685 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24685
          have b7e24695 : x = (k x y) ∨ (M.op x y) = (k x x) := by
            first
            | (have r₁ := b7e24687
               have r₂ := b7e22
               grind)
            | exact resolve b7e24687 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24687
          have b7e30094 : (σ y) = (σ (k x y)) ∨ (M.op x y) = (k x x) := by
            first
            | (have i₁ := b7e945
               have i₂ := b7e24695
               grind)
            | exact superpose b7e24695 b7e945
            | exact resolve b7e945 b7e24695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e945 b7e24695
          have b7e30101 : (M.op x y) = (k x x) := by
            first
            | (have r₁ := b7e30094
               have r₂ := b7e74
               grind)
            | exact resolve b7e30094 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30094
          have b7e32171 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e30101
               grind)
            | exact superpose b7e30101 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e30101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32172 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e32171
          have b7e39476 : (M.op y y) = (M.op y (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e2375 x y
               have i₂ := b7e32172
               grind)
            | exact superpose b7e32172 b7e2375
            | exact resolve b7e2375 b7e32172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32172
          have b7e39482 : (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e39476
               have i₂ := b7e2375 x x
               grind)
            | exact superpose b7e2375 b7e39476
            | exact resolve b7e39476 b7e2375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2375 b7e39476
          have b7e39560 : y = (M.op y x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e39482
               have i₂ := b7e2126
               grind)
            | exact superpose b7e2126 b7e39482
            | exact resolve b7e39482 b7e2126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2126 b7e39482
          have b7e39616 : x = (M.op x x) := by
            first
            | (have r₁ := b7e39560
               have r₂ := b7e22
               grind)
            | exact resolve b7e39560 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39560
          have b7e39935 : x = (k x x) := by grind
          clear b7e39616
          have b7e40221 : x = (M.op x y) := by
            first
            | (have i₁ := b7e30101
               have i₂ := b7e39935
               grind)
            | exact superpose b7e39935 b7e30101
            | exact resolve b7e30101 b7e39935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30101 b7e39935
          have b7e40293 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1268
               have i₂ := b7e40221
               grind)
            | exact superpose b7e40221 b7e1268
            | exact resolve b7e1268 b7e40221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1268 b7e40221
          have b7e40468 : False := by grind
          exact b7e40468
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e1863 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e1864 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1863
               have r₂ := b8e24
               grind)
            | exact resolve b8e1863 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1863
          have b8e1865 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1864
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1864
            | exact resolve b8e1864 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1864
          have b8e1866 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1865
               grind)
            | exact superpose b8e1865 b8e20
            | exact resolve b8e20 b8e1865
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1865
          have b8e2135 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1866
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1866
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1866 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1866
          have b8e2136 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e2135
          have b8e2138 : y = (M.op y x) := by
            first
            | (have r₁ := b8e2136
               have r₂ := b8e21
               grind)
            | exact resolve b8e2136 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2136
          have b8e2140 : False := by grind
          exact b8e2140
