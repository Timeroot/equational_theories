import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),m(X,X)) = m(m(Y,Y),m(Y,Y)) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxpxx_ppyypyy_x_y_pxy_x_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 0))) (((Lf 1) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 0))) (((Lf 1) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) (M.op a a) ≠ M.op (M.op b b) (M.op b b) ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a a)) (M.op (M.op b b) (M.op b b))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) (M.op a a) = M.op (M.op b b) (M.op b b) ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a a)) (M.op (M.op b b) (M.op b b))).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) (M.op a a) = M.op (M.op b b) (M.op b b) ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a a)) (M.op (M.op b b) (M.op b b))).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) (M.op x x)) (M.op (M.op y y) (M.op y y)) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y y) (M.op y y)) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e22 X0 X1
           grind)
        | exact superpose b0e22 b0e12
        | exact resolve b0e12 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e37 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x x) (M.op x x)) ∨ (k y X0) = (M.op y X0) := by
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
      have b0e39 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x x) (M.op x x)) ∨ (k X0 y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
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
      have b0e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e40 (σ X0)
           grind)
        | exact superpose b0e40 b0e17
        | exact resolve b0e17 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e42 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e42
        | exact resolve b0e42 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e42
      have b0e52 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
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
      have b0e57 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e52 X0
           have i₂ := b0e47 x
           grind)
        | exact superpose b0e47 b0e52
        | (have j0 := b0e52 X0
           grind)
        | exact resolve b0e52 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e61 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (σ (M.op (M.op x x) (M.op x x))) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e57 X0
           have i₂ := b0e47 (M.op x x)
           grind)
        | exact superpose b0e47 b0e57
        | (have j0 := b0e57 X0
           grind)
        | exact resolve b0e57 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e67 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e27
        | exact resolve b0e27 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e97 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X1 X2
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X2 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X0
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X1) (M.op X1 X1))
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e98 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X1 X2
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X2
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X0
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X1) (M.op X1 X1))
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e169 : (k y x) = (M.op y x) := by
        first
        | (have j0 := b0e37 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e187 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b0e39 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e219 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x x))) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (k (σ y) (σ X0)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e61 (σ X0)
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e61
        | (have j0 := b0e61 (σ X0)
           grind)
        | exact resolve b0e61 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e220 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x x))) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (σ y) (σ X0)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e219 X0
           have i₂ := b0e47 (M.op X0 X0)
           grind)
        | exact superpose b0e47 b0e219
        | (have j0 := b0e219 X0
           grind)
        | (have r₁ := b0e219 x
           have r₂ := b0e47 (M.op x x)
           grind)
        | exact resolve b0e219 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e219
      have b0e228 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x x))) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e220 X0
           have i₂ := b0e17 y X0
           grind)
        | exact superpose b0e17 b0e220
        | (have j0 := b0e220 X0
           grind)
        | exact resolve b0e220 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e220
      have b0e713 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e97 X0 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97
      have b0e822 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e98 X1 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98
      have b0e3018 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e713 (σ X0) (σ X1)
           grind)
        | exact superpose b0e713 b0e17
        | (have j1 := b0e713 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e713
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e713
      have b0e3071 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e3018 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e3018
        | (have j0 := b0e3018 X0 X1
           grind)
        | exact resolve b0e3018 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3018
      have b0e3372 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e822 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e301147 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have j0 := b0e3071 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3071
      have b0e302835 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e301147 (τ X1) (τ X0)
           have i₂ := b0e67 X0 X1
           grind)
        | exact superpose b0e67 b0e301147
        | (have j0 := b0e301147 (τ X0) (τ X1)
           grind)
        | exact resolve b0e301147 b0e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67 b0e301147
      have b0e302925 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e302835 X0 X1
           have i₂ := b0e23 X0 (τ X1)
           grind)
        | exact superpose b0e23 b0e302835
        | (have j0 := b0e302835 X0 X1
           grind)
        | exact resolve b0e302835 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e302835
      have b0e302933 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e302925 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e302925
        | (have j0 := b0e302925 X0 X1
           grind)
        | exact resolve b0e302925 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302925
      have b0e302939 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e302933 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e302933
        | (have j0 := b0e302933 X0 X1
           grind)
        | (have r₁ := b0e302933 X1 X1
           have r₂ := b0e13 (k X1 X1)
           grind)
        | exact resolve b0e302933 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302933
      have b0e302943 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e302939 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e302939
        | (have j0 := b0e302939 X0 X1
           grind)
        | exact resolve b0e302939 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302939
      have b0e302945 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e302943 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e302943
        | (have j0 := b0e302943 X0 X1
           grind)
        | exact resolve b0e302943 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302943
      have b0e302947 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e302945 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e302945
        | (have j0 := b0e302945 X0 X1
           grind)
        | exact resolve b0e302945 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302945
      have b0e302949 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e302947 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e302947
        | (have j0 := b0e302947 X0 X1
           grind)
        | exact resolve b0e302947 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302947
      have b0e302951 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e302949 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e302949
        | (have j0 := b0e302949 X0 X1
           grind)
        | exact resolve b0e302949 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302949
      have b0e303819 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e302951 X0 X1
           have i₂ := b0e822 X0 X1
           grind)
        | exact superpose b0e822 b0e302951
        | (have j0 := b0e302951 X1 X0
           have j1 := b0e822 X1 X0
           grind)
        | (have r₁ := b0e302951 X0 X1
           have r₂ := b0e822 (k X0 X1) (k X1 X0)
           grind)
        | (have r₁ := b0e302951 X0 X1
           have r₂ := b0e822 (k X1 X0) (k X0 X1)
           grind)
        | exact resolve b0e302951 b0e822
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e822 b0e302951
      have b0e304008 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e303819 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e303819
      have b0e304036 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e304008 X0 X1
           have j1 := b0e3372 X1 X0
           grind)
        | (have r₁ := b0e304008 X0 X1
           have r₂ := b0e3372 X0 X1
           grind)
        | (have r₁ := b0e304008 X0 X1
           have r₂ := b0e3372 (k X0 X1) (M.op X0 X1)
           grind)
        | (have r₁ := b0e304008 X0 X1
           have r₂ := b0e3372 (M.op X0 X1) (k X0 X1)
           grind)
        | exact resolve b0e304008 b0e3372
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3372 b0e304008
      have b0e305335 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e304036 (σ X0) (σ X1)
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e304036
        | (have j0 := b0e304036 (σ X0) (σ X1)
           grind)
        | exact resolve b0e304036 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e304036
      have b0e305444 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e305335 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e305335
        | (have j0 := b0e305335 X0 X1
           grind)
        | exact resolve b0e305335 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e305335
      have b0e834158 : (σ (k y x)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b0e228 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228
      have b0e834160 : (σ (M.op y x)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e834158
           have i₂ := b0e169
           grind)
        | exact superpose b0e169 b0e834158
        | exact resolve b0e834158 b0e169
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e834158
      have b0e835464 : (σ (k y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e305444 y x
           have i₂ := b0e834160
           grind)
        | exact superpose b0e834160 b0e305444
        | (have j0 := b0e305444 y x
           grind)
        | exact resolve b0e305444 b0e834160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e305444 b0e834160
      have b0e835493 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e835464
           have i₂ := b0e169
           grind)
        | exact superpose b0e169 b0e835464
        | exact resolve b0e835464 b0e169
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e169 b0e835464
      have b0e835494 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
      clear b0e835493
      have b0e835518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e835494
           have i₂ := b0e187
           grind)
        | exact superpose b0e187 b0e835494
        | exact resolve b0e835494 b0e187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e187 b0e835494
      have b0e835535 : (σ x) = (σ y) := by
        first
        | (have r₁ := b0e835518
           have r₂ := b0e18
           grind)
        | exact resolve b0e835518 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e835518
      have b0e836341 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e835535
           grind)
        | exact superpose b0e835535 b0e18
        | exact resolve b0e18 b0e835535
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e836388 : y = (τ (σ x)) := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e835535
           grind)
        | exact superpose b0e835535 b0e12
        | exact resolve b0e12 b0e835535
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e835535
      have b0e836612 : x = y := by
        first
        | (have i₁ := b0e836388
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e836388
        | exact resolve b0e836388 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e836388
      have b0e836614 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e836341
           have i₂ := b0e47 x
           grind)
        | exact superpose b0e47 b0e836341
        | exact resolve b0e836341 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e836341
      have b0e836615 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e836614
           have i₂ := b0e836612
           grind)
        | exact superpose b0e836612 b0e836614
        | exact resolve b0e836614 b0e836612
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e836612 b0e836614
      have b0e836616 : False := by grind
      exact b0e836616
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y y) (M.op y y)) := by grind
        have b2e21 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e34 (σ X0)
             grind)
          | exact superpose b2e34 b2e18
          | exact resolve b2e18 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e36 X0
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e36
          | exact resolve b2e36 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e36
        have b2e174 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e39 y
             grind)
          | exact superpose b2e39 b2e21
          | exact resolve b2e21 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e189 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b2e174
             have i₂ := b2e39 (M.op y y)
             grind)
          | exact superpose b2e39 b2e174
          | exact resolve b2e174 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174
        have b2e190 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (σ (M.op (M.op x x) (M.op x x))) := by
          first
          | (have i₁ := b2e189
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e189
          | exact resolve b2e189 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e189
        have b2e191 : (M.op (σ (M.op x x)) (σ (M.op x x))) ≠ (σ (M.op (M.op x x) (M.op x x))) := by
          first
          | (have i₁ := b2e190
             have i₂ := b2e39 x
             grind)
          | exact superpose b2e39 b2e190
          | exact resolve b2e190 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e190
        have b2e192 : False := by grind
        exact b2e192
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) with h1a | h1a
      · have b3e20 : (M.op (M.op x x) (M.op x x)) ≠ (M.op (M.op y y) (M.op y y)) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op (M.op x x) (M.op x x)) ≠ (M.op (M.op y y) (M.op y y)) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e30 (σ X0)
             grind)
          | exact superpose b6e30 b6e18
          | exact resolve b6e18 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e30 X0
             grind)
          | exact superpose b6e30 b6e32
          | exact resolve b6e32 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e32
        have b6e150 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e35 y
             grind)
          | exact superpose b6e35 b6e22
          | exact resolve b6e22 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e161 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b6e150
             have i₂ := b6e35 (M.op y y)
             grind)
          | exact superpose b6e35 b6e150
          | exact resolve b6e150 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e150
        have b6e163 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b6e161
             have i₂ := b6e35 x
             grind)
          | exact superpose b6e35 b6e161
          | exact resolve b6e161 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e161
        have b6e164 : (σ (M.op (M.op x x) (M.op x x))) = (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b6e163
             have i₂ := b6e35 (M.op x x)
             grind)
          | exact superpose b6e35 b6e163
          | exact resolve b6e163 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e163
        have b6e2650 : (M.op (M.op y y) (M.op y y)) = (τ (σ (M.op (M.op x x) (M.op x x)))) := by
          first
          | (have i₁ := b6e13 (M.op (M.op y y) (M.op y y))
             have i₂ := b6e164
             grind)
          | exact superpose b6e164 b6e13
          | exact resolve b6e13 b6e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e164
        have b6e2687 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y y) (M.op y y)) := by
          first
          | (have i₁ := b6e2650
             have i₂ := b6e13 (M.op (M.op x x) (M.op x x))
             grind)
          | exact superpose b6e13 b6e2650
          | exact resolve b6e2650 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2650
        have b6e2688 : False := by grind
        exact b6e2688
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
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
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op (M.op x x) (M.op x x)) ≠ (M.op (M.op y y) (M.op y y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e40 (σ X0)
               grind)
            | exact superpose b8e40 b8e19
            | exact resolve b8e19 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e42 X0
               have i₂ := b8e40 X0
               grind)
            | exact superpose b8e40 b8e42
            | exact resolve b8e42 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e42
          have b8e72 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x x) (M.op x x)) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 y X0
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 y
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 y X0
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op (M.op x x) (M.op x x)) (M.op (M.op y y) (M.op y y))
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X1 X2
               have i₂ := b8e18 X2 X0
               grind)
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X2 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X0
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X1) (M.op X1 X1))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X1 X2
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X2
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X0
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X1) (M.op X1 X1))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e78 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x x) (M.op x x)) ∨ (k X0 y) = (M.op y X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 y
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 X0 y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op (M.op x x) (M.op x x)) (M.op (M.op y y) (M.op y y))
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e89 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e84 X0 X0
               have i₂ := b8e47 X0
               grind)
            | exact superpose b8e47 b8e84
            | (have j0 := b8e84 X0 X1
               grind)
            | exact resolve b8e84 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e94 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89 X0 X1
               have i₂ := b8e47 (M.op X1 X1)
               grind)
            | exact superpose b8e47 b8e89
            | (have j0 := b8e89 X0 X1
               grind)
            | exact resolve b8e89 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e98 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e94 X0 X1
               have i₂ := b8e47 X0
               grind)
            | exact superpose b8e47 b8e94
            | (have j0 := b8e94 X0 X1
               grind)
            | exact resolve b8e94 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94
          have b8e100 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e98 X0 X1
               have i₂ := b8e47 (M.op X0 X0)
               grind)
            | exact superpose b8e47 b8e98
            | (have j0 := b8e98 X0 X1
               grind)
            | exact resolve b8e98 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47 b8e98
          have b8e127 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e72 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e128 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e127
               have r₂ := b8e22
               grind)
            | exact resolve b8e127 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e135 : (k x y) = (M.op y x) ∨ x = y := by
            first
            | (have j0 := b8e78 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e136 : (k x y) = (M.op y x) := by
            first
            | (have r₁ := b8e135
               have r₂ := b8e22
               grind)
            | exact resolve b8e135 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e198 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e235 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e74 X1 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e409 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (M.op (M.op X1 X1) (M.op X1 X1))
               have i₂ := b8e100 X0 X1
               grind)
            | (have i₁ := b8e14 (M.op (M.op X0 X0) (M.op X0 X0))
               have i₂ := b8e100 X0 X1
               grind)
            | exact superpose b8e100 b8e14
            | (have j1 := b8e100 X0 X1
               grind)
            | exact resolve b8e14 b8e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100
          have b8e428 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e409 X0 X1
               have i₂ := b8e14 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact superpose b8e14 b8e409
            | (have j0 := b8e409 X0 X1
               grind)
            | exact resolve b8e409 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e409
          have b8e1728 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e198 (σ X0) (σ X1)
               grind)
            | exact superpose b8e198 b8e19
            | (have j1 := b8e198 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e198
          have b8e1765 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e1728 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1728
            | (have j0 := b8e1728 X0 X1
               grind)
            | exact resolve b8e1728 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1728
          have b8e1901 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e235 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e235
          have b8e4064 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x x) (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (σ (k X0 y)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e428 y X0
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e428 X0 y
               grind)
            | exact superpose b8e428 b8e21
            | (have j1 := b8e428 y X0
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e428 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e428 y x
               grind)
            | exact resolve b8e21 b8e428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e428
          have b8e82088 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1765 x y
               grind)
            | exact superpose b8e1765 b8e20
            | (have j1 := b8e1765 x y
               grind)
            | exact resolve b8e20 b8e1765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e82100 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e1901 (σ X0) (σ X1)
               have i₂ := b8e1765 X0 X1
               grind)
            | exact superpose b8e1765 b8e1901
            | (have j0 := b8e1901 (σ (k X0 X1)) (k (σ X1) (σ X0))
               have j1 := b8e1765 X1 X0
               grind)
            | exact resolve b8e1901 b8e1765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1901
          have b8e82131 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b8e1765 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1765
          have b8e82163 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e82100 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82100
          have b8e82195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e82163 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e82163
            | (have j0 := b8e82163 X0 X1
               grind)
            | exact resolve b8e82163 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82163
          have b8e82204 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e82088
               have r₂ := b8e24
               grind)
            | exact resolve b8e82088 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82088
          have b8e82257 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e82195 X0 X1
               have j1 := b8e82131 X1 X0
               grind)
            | (have r₁ := b8e82195 X0 X1
               have r₂ := b8e82131 X0 X1
               grind)
            | (have r₁ := b8e82195 X1 X0
               have r₂ := b8e82131 X0 X1
               grind)
            | (have r₁ := b8e82195 (k X0 X1) (k X1 X0)
               have r₂ := b8e82131 X0 X1
               grind)
            | exact resolve b8e82195 b8e82131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82131 b8e82195
          have b8e82261 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e82204
               have i₂ := b8e128
               grind)
            | exact superpose b8e128 b8e82204
            | exact resolve b8e82204 b8e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82204
          have b8e82262 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b8e82261
          have b8e82299 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e82262
               have i₂ := b8e136
               grind)
            | exact superpose b8e136 b8e82262
            | exact resolve b8e82262 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82262
          have b8e84200 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e82299
               grind)
            | exact superpose b8e82299 b8e20
            | exact resolve b8e20 b8e82299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e143202 : (σ (k x y)) ≠ (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e82257 x y
               have i₂ := b8e82299
               grind)
            | exact superpose b8e82299 b8e82257
            | (have j0 := b8e82257 x y
               grind)
            | exact resolve b8e82257 b8e82299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82257 b8e82299
          have b8e143237 : (σ (k x y)) ≠ (σ (M.op y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e143202
               have r₂ := b8e24
               grind)
            | exact resolve b8e143202 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143202
          have b8e143264 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e143237
               have i₂ := b8e136
               grind)
            | exact superpose b8e136 b8e143237
            | exact resolve b8e143237 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143237
          have b8e143265 : (σ (k y x)) = (M.op (σ y) (σ x)) := by grind
          clear b8e143264
          have b8e143283 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e143265
               have i₂ := b8e128
               grind)
            | exact superpose b8e128 b8e143265
            | exact resolve b8e143265 b8e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128 b8e143265
          have b8e5435208 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e4064 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4064
          have b8e5435209 : (σ (k x y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e5435208
               have r₂ := b8e24
               grind)
            | exact resolve b8e5435208 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5435208
          have b8e5435210 : (σ (M.op x y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e5435209
               have i₂ := b8e143283
               grind)
            | exact superpose b8e143283 b8e5435209
            | exact resolve b8e5435209 b8e143283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143283 b8e5435209
          have b8e5435211 : (σ (M.op x y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e5435210
               have i₂ := b8e136
               grind)
            | exact superpose b8e136 b8e5435210
            | exact resolve b8e5435210 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136 b8e5435210
          have b8e5435212 : False := by grind
          exact b8e5435212

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),m(X,X)) = m(m(Y,Y),m(Y,Y)) then m(Y,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxpxx_ppyypyy_x_y_pyx_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 0))) (((Lf 1) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 0))) (((Lf 1) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) (M.op a a) ≠ M.op (M.op b b) (M.op b b) ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a a)) (M.op (M.op b b) (M.op b b))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) (M.op a a) = M.op (M.op b b) (M.op b b) ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a a)) (M.op (M.op b b) (M.op b b))).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) (M.op a a) = M.op (M.op b b) (M.op b b) ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) (M.op a a)) (M.op (M.op b b) (M.op b b))).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) (M.op x x)) (M.op (M.op y y) (M.op y y)) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y y) (M.op y y)) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e37 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x x) (M.op x x)) ∨ (k y X0) = (M.op X0 y) := by
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
      have b0e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e40 (σ X0)
           grind)
        | exact superpose b0e40 b0e17
        | exact resolve b0e17 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e42 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e42
        | exact resolve b0e42 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e42
      have b0e52 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
      have b0e57 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e52 X0
           have i₂ := b0e47 x
           grind)
        | exact superpose b0e47 b0e52
        | (have j0 := b0e52 X0
           grind)
        | exact resolve b0e52 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e61 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (σ (M.op (M.op x x) (M.op x x))) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e57 X0
           have i₂ := b0e47 (M.op x x)
           grind)
        | exact superpose b0e47 b0e57
        | (have j0 := b0e57 X0
           grind)
        | exact resolve b0e57 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e169 : (M.op x y) = (k y x) := by
        first
        | (have j0 := b0e37 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e219 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x x))) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e61 (σ X0)
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e61
        | (have j0 := b0e61 (σ X0)
           grind)
        | exact resolve b0e61 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e220 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x x))) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e219 X0
           have i₂ := b0e47 (M.op X0 X0)
           grind)
        | exact superpose b0e47 b0e219
        | (have j0 := b0e219 X0
           grind)
        | (have r₁ := b0e219 x
           have r₂ := b0e47 (M.op x x)
           grind)
        | exact resolve b0e219 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e219
      have b0e228 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x x))) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ X0) (σ y)) = (σ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e220 X0
           have i₂ := b0e17 y X0
           grind)
        | exact superpose b0e17 b0e220
        | (have j0 := b0e220 X0
           grind)
        | exact resolve b0e220 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e220
      have b0e810222 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have j0 := b0e228 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228
      have b0e810224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e810222
           have i₂ := b0e169
           grind)
        | exact superpose b0e169 b0e810222
        | exact resolve b0e810222 b0e169
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e169 b0e810222
      have b0e810229 : False := by grind
      exact b0e810229
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y y) (M.op y y)) := by grind
        have b2e21 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e34 (σ X0)
             grind)
          | exact superpose b2e34 b2e18
          | exact resolve b2e18 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e36 X0
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e36
          | exact resolve b2e36 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e36
        have b2e174 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e39 y
             grind)
          | exact superpose b2e39 b2e21
          | exact resolve b2e21 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e189 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b2e174
             have i₂ := b2e39 (M.op y y)
             grind)
          | exact superpose b2e39 b2e174
          | exact resolve b2e174 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174
        have b2e190 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (σ (M.op (M.op x x) (M.op x x))) := by
          first
          | (have i₁ := b2e189
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e189
          | exact resolve b2e189 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e189
        have b2e191 : (M.op (σ (M.op x x)) (σ (M.op x x))) ≠ (σ (M.op (M.op x x) (M.op x x))) := by
          first
          | (have i₁ := b2e190
             have i₂ := b2e39 x
             grind)
          | exact superpose b2e39 b2e190
          | exact resolve b2e190 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e190
        have b2e192 : False := by grind
        exact b2e192
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) with h1a | h1a
      · have b3e20 : (M.op (M.op x x) (M.op x x)) ≠ (M.op (M.op y y) (M.op y y)) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op (M.op x x) (M.op x x)) ≠ (M.op (M.op y y) (M.op y y)) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e30 (σ X0)
             grind)
          | exact superpose b6e30 b6e18
          | exact resolve b6e18 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e30 X0
             grind)
          | exact superpose b6e30 b6e32
          | exact resolve b6e32 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e32
        have b6e150 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e35 y
             grind)
          | exact superpose b6e35 b6e22
          | exact resolve b6e22 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e161 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b6e150
             have i₂ := b6e35 (M.op y y)
             grind)
          | exact superpose b6e35 b6e150
          | exact resolve b6e150 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e150
        have b6e163 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b6e161
             have i₂ := b6e35 x
             grind)
          | exact superpose b6e35 b6e161
          | exact resolve b6e161 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e161
        have b6e164 : (σ (M.op (M.op x x) (M.op x x))) = (σ (M.op (M.op y y) (M.op y y))) := by
          first
          | (have i₁ := b6e163
             have i₂ := b6e35 (M.op x x)
             grind)
          | exact superpose b6e35 b6e163
          | exact resolve b6e163 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e163
        have b6e2650 : (M.op (M.op y y) (M.op y y)) = (τ (σ (M.op (M.op x x) (M.op x x)))) := by
          first
          | (have i₁ := b6e13 (M.op (M.op y y) (M.op y y))
             have i₂ := b6e164
             grind)
          | exact superpose b6e164 b6e13
          | exact resolve b6e13 b6e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e164
        have b6e2687 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y y) (M.op y y)) := by
          first
          | (have i₁ := b6e2650
             have i₂ := b6e13 (M.op (M.op x x) (M.op x x))
             grind)
          | exact superpose b6e13 b6e2650
          | exact resolve b6e2650 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2650
        have b6e2688 : False := by grind
        exact b6e2688
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
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
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op (M.op x x) (M.op x x)) ≠ (M.op (M.op y y) (M.op y y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e40 (σ X0)
               grind)
            | exact superpose b8e40 b8e19
            | exact resolve b8e19 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e42 X0
               have i₂ := b8e40 X0
               grind)
            | exact superpose b8e40 b8e42
            | exact resolve b8e42 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e42
          have b8e78 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x x) (M.op x x)) ∨ (k X0 y) = (M.op X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 y
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 X0 y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op (M.op x x) (M.op x x)) (M.op (M.op y y) (M.op y y))
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) ∨ (σ X0) = (σ X1) := by
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
          have b8e89 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e84 X0 X0
               have i₂ := b8e47 X0
               grind)
            | exact superpose b8e47 b8e84
            | (have j0 := b8e84 X0 X1
               grind)
            | exact resolve b8e84 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e94 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89 X0 X1
               have i₂ := b8e47 (M.op X1 X1)
               grind)
            | exact superpose b8e47 b8e89
            | (have j0 := b8e89 X0 X1
               grind)
            | exact resolve b8e89 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e98 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e94 X0 X1
               have i₂ := b8e47 X0
               grind)
            | exact superpose b8e47 b8e94
            | (have j0 := b8e94 X0 X1
               grind)
            | exact resolve b8e94 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94
          have b8e100 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e98 X0 X1
               have i₂ := b8e47 (M.op X0 X0)
               grind)
            | exact superpose b8e47 b8e98
            | (have j0 := b8e98 X0 X1
               grind)
            | exact resolve b8e98 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47 b8e98
          have b8e135 : (M.op x y) = (k x y) ∨ x = y := by
            first
            | (have j0 := b8e78 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e136 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e135
               have r₂ := b8e22
               grind)
            | exact resolve b8e135 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e409 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (M.op (M.op X1 X1) (M.op X1 X1))
               have i₂ := b8e100 X1 X0
               grind)
            | (have i₁ := b8e14 (M.op (M.op X1 X1) (M.op X1 X1))
               have i₂ := b8e100 X0 X1
               grind)
            | exact superpose b8e100 b8e14
            | (have j1 := b8e100 X1 X0
               grind)
            | exact resolve b8e14 b8e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100
          have b8e428 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e409 X0 X1
               have i₂ := b8e14 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact superpose b8e14 b8e409
            | (have j0 := b8e409 X0 X1
               grind)
            | exact resolve b8e409 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e409
          have b8e4064 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x x) (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e428 y X0
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e428 X0 y
               grind)
            | exact superpose b8e428 b8e21
            | (have j1 := b8e428 y X0
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e428 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e428 y x
               grind)
            | exact resolve b8e21 b8e428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e428
          have b8e5407983 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e4064 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4064
          have b8e5407984 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e5407983
               have r₂ := b8e24
               grind)
            | exact resolve b8e5407983 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5407983
          have b8e5407985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e5407984
               have i₂ := b8e136
               grind)
            | exact superpose b8e136 b8e5407984
            | exact resolve b8e5407984 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136 b8e5407984
          have b8e5407986 : False := by grind
          exact b8e5407986
