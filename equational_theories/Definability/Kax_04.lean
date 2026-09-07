import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation326`: `x ◇ y = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_x_pxy_Equation326 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law326 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law326.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
        intro X0
        grind
      have b0e69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e70 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op X1 X1) X1
           have i₂ := b0e16 X0 (M.op X1 X1)
           grind)
        | (have i₁ := b0e11 X0 X1
           have i₂ := b0e16 (M.op X0 (M.op X1 X1)) X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X0 X0) X1
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e11 X0 X1
           have i₂ := b0e16 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e76 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        grind
      have b0e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b0e87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X1 X1)) ∨ (M.op (M.op X1 X1) X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e70 X0 X1
           have i₂ := b0e11 X0 X1
           grind)
        | exact superpose b0e11 b0e70
        | (have j0 := b0e70 X0 X1
           grind)
        | exact resolve b0e70 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e105 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e31 X0 X1
           grind)
        | exact superpose b0e31 b0e12
        | exact resolve b0e12 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e119 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e105 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e105
        | exact resolve b0e105 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e330 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = X1 ∨ (k X1 X0) = X0 := by
        intro X0 X1
        grind
      clear b0e69
      have b0e387 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e43 X0
           have i₂ := b0e76 X0 X1
           grind)
        | (have i₁ := b0e43 X0
           have i₂ := b0e76 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e76 b0e43
        | (have j1 := b0e76 X1 X0
           grind)
        | exact resolve b0e43 b0e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e76
      have b0e409 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e387 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e387
      have b0e1097 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) ∨ (M.op x x) = X1 ∨ (M.op X1 x) = (k X1 x) := by
        intro X0 X1
        first
        | (have i₁ := b0e26 X0
           have i₂ := b0e75 x X0 X1
           grind)
        | (have i₁ := b0e26 X1
           have i₂ := b0e75 X0 X1 x
           grind)
        | exact superpose b0e75 b0e26
        | (have j1 := b0e75 x X1 X1
           grind)
        | exact resolve b0e26 b0e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e1211 : ∀ X0 X1 : G, (M.op x y) = X1 ∨ (M.op X0 X1) = (M.op X0 y) ∨ (M.op X1 x) = (k X1 x) := by
        intro X0 X1
        first
        | (have i₁ := b0e1097 X0 X1
           have i₂ := b0e26 x
           grind)
        | exact superpose b0e26 b0e1097
        | (have j0 := b0e1097 X0 X1
           grind)
        | exact resolve b0e1097 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1097
      have b0e1244 : ∀ X0 X1 : G, (k X1 x) = (M.op X1 y) ∨ (M.op X0 X1) = (M.op X0 y) ∨ (M.op x y) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1211 X0 X1
           have i₂ := b0e26 X1
           grind)
        | exact superpose b0e26 b0e1211
        | (have j0 := b0e1211 X0 X1
           grind)
        | exact resolve b0e1211 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1211
      have b0e1438 : ∀ X0 : G, (M.op X0 y) = (k X0 x) ∨ (M.op X0 X0) = x ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e87 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e87
        | exact resolve b0e87 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e2612 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e81 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e2613 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e2612 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2612
      have b0e6212 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e330 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e330
      have b0e6214 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e6212 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6212
      have b0e6326 : x ≠ (M.op x y) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e6214 x
           have i₂ := b0e26 x
           grind)
        | exact superpose b0e26 b0e6214
        | (have j0 := b0e6214 x
           grind)
        | exact resolve b0e6214 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6214
      have b0e6616 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e409 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e409
      have b0e9690 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e6616 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6616
      have b0e9794 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e9690 (σ x)
           have i₂ := b0e17 x x
           grind)
        | exact superpose b0e17 b0e9690
        | exact resolve b0e9690 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e9819 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
        intro X0
        first
        | (have i₁ := b0e31 X0 (τ X0)
           have i₂ := b0e9690 (τ X0)
           grind)
        | exact superpose b0e9690 b0e31
        | (have j1 := b0e9690 (τ X0)
           grind)
        | exact resolve b0e31 b0e9690
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e9690
      have b0e9829 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
        intro X0
        first
        | (have i₁ := b0e9819 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e9819
        | (have j0 := b0e9819 X0
           grind)
        | exact resolve b0e9819 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9819
      have b0e9845 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e9829 X0
           have i₂ := b0e119 X0 X0
           grind)
        | exact superpose b0e119 b0e9829
        | (have j0 := b0e9829 X0
           grind)
        | exact resolve b0e9829 b0e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e119 b0e9829
      have b0e15420 : ∀ X0 : G, x = (M.op X0 y) ∨ (M.op X0 y) = (k X0 x) ∨ (M.op x y) = X0 ∨ (M.op X0 y) = (k X0 x) ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1438 X0
           have i₂ := b0e1244 X0 X0
           grind)
        | (have i₁ := b0e1438 y
           have i₂ := b0e1244 y x
           grind)
        | exact superpose b0e1244 b0e1438
        | (have j0 := b0e1438 X0
           have j1 := b0e1244 X0 X0
           grind)
        | exact resolve b0e1438 b0e1244
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1244 b0e1438
      have b0e15542 : ∀ X0 : G, (M.op X0 y) = (k X0 x) ∨ x = (M.op X0 y) ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have j0 := b0e15420 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15420
      have b0e95390 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e27 (σ x)
           have i₂ := b0e9794 x
           grind)
        | exact superpose b0e9794 b0e27
        | (have j1 := b0e9794 x
           grind)
        | exact resolve b0e27 b0e9794
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9794
      have b0e145471 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (τ (k (σ X0) (σ X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e9845 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e9845
        | exact resolve b0e9845 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9845
      have b0e145489 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (τ (k (σ X0) (σ X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e145471 X0
           have i₂ := b0e17 X0 X0
           grind)
        | exact superpose b0e17 b0e145471
        | (have j0 := b0e145471 X0
           grind)
        | exact resolve b0e145471 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145471
      have b0e145491 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e145489 X0
           have i₂ := b0e105 (σ X0) X0
           grind)
        | exact superpose b0e105 b0e145489
        | (have j0 := b0e145489 X0
           grind)
        | exact resolve b0e145489 b0e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105 b0e145489
      have b0e145493 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e145491 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e145491
        | (have j0 := b0e145491 X0
           grind)
        | exact resolve b0e145491 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145491
      have b0e179207 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e95390
           grind)
        | exact superpose b0e95390 b0e18
        | exact resolve b0e18 b0e95390
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95390
      have b0e179955 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e179207
           have i₂ := b0e145493 x
           grind)
        | exact superpose b0e145493 b0e179207
        | (have j1 := b0e145493 x
           grind)
        | exact resolve b0e179207 b0e145493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145493 b0e179207
      have b0e179957 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e179955
           have i₂ := b0e26 x
           grind)
        | exact superpose b0e26 b0e179955
        | exact resolve b0e179955 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179955
      have b0e179958 : (σ x) = (σ (M.op x x)) ∨ x = (k x x) := by grind
      clear b0e179957
      have b0e179963 : (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e179958
           have i₂ := b0e26 x
           grind)
        | exact superpose b0e26 b0e179958
        | exact resolve b0e179958 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e179958
      have b0e181245 : (M.op x y) = (τ (σ x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e179963
           grind)
        | exact superpose b0e179963 b0e12
        | exact resolve b0e12 b0e179963
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179963
      have b0e181285 : x = (M.op x y) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e181245
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e181245
        | exact resolve b0e181245 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e181245
      have b0e181286 : x = (k x x) := by
        first
        | (have r₁ := b0e181285
           have r₂ := b0e6326
           grind)
        | exact resolve b0e181285 b0e6326
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6326 b0e181285
      have b0e182155 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15542 x
           have i₂ := b0e181286
           grind)
        | exact superpose b0e181286 b0e15542
        | (have j0 := b0e15542 x
           grind)
        | exact resolve b0e15542 b0e181286
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15542
      have b0e182157 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e2613 x
           have i₂ := b0e181286
           grind)
        | exact superpose b0e181286 b0e2613
        | (have j0 := b0e2613 x
           grind)
        | exact resolve b0e2613 b0e181286
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2613 b0e181286
      have b0e182228 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e182157
      have b0e182229 : x = (M.op x y) := by grind
      clear b0e182155
      have b0e182305 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e182228
           have i₂ := b0e27 (σ x)
           grind)
        | exact superpose b0e27 b0e182228
        | exact resolve b0e182228 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e182228
      have b0e185005 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e182305
           grind)
        | exact superpose b0e182305 b0e18
        | exact resolve b0e18 b0e182305
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e182305
      have b0e185135 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e185005
           have i₂ := b0e182229
           grind)
        | exact superpose b0e182229 b0e185005
        | exact resolve b0e185005 b0e182229
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e182229 b0e185005
      have b0e185136 : False := by grind
      exact b0e185136
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b1e25 : y = (k x y) := by grind
        have b1e46 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e53 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e21
             grind)
          | exact resolve b1e46 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e57 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e58 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e57
          | exact resolve b1e57 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e57
        have b1e59 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e19
          | exact resolve b1e19 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e22
          | exact resolve b1e22 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e13
          | exact resolve b1e13 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : x = y := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e63
          | exact resolve b1e63 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e67 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e59
          | exact resolve b1e59 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e60
        have b1e68 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e67
             have i₂ := b1e64
             grind)
          | exact superpose b1e64 b1e67
          | exact resolve b1e67 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e67
        have b1e69 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e68
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e68
          | exact resolve b1e68 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e70 : False := by grind
        exact b1e70
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : y = (k x y) := by grind
        have b2e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e53 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e33 X0 X1
             grind)
          | exact superpose b2e33 b2e13
          | exact resolve b2e13 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e72 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
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
        have b2e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e110 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          grind
        clear b2e53
        have b2e116 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e110 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e110
          | exact resolve b2e110 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e110
        have b2e779 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e72 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72
        have b2e780 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e779
             have r₂ := b2e22
             grind)
          | exact resolve b2e779 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e779
        have b2e781 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e780
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e780
          | exact resolve b2e780 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e780
        have b2e782 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e781
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e781
          | exact resolve b2e781 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e781
        have b2e2185 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e82 y y
             grind)
          | exact superpose b2e82 b2e21
          | (have j1 := b2e82 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e82 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e82 y x
             grind)
          | exact resolve b2e21 b2e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e2344 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e2185
        have b2e4863 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e2344
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e2344
          | (have j1 := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e2344 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2344
        have b2e4874 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e4863
        have b2e4891 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e4874
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4874
          | exact resolve b2e4874 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4874
        have b2e4892 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e4891
        have b2e4907 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e4892
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4892
          | exact resolve b2e4892 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4892
        have b2e4940 : y = (k (τ (σ y)) y) ∨ x = y := by
          first
          | (have i₁ := b2e116 y
             have i₂ := b2e4907
             grind)
          | exact superpose b2e4907 b2e116
          | exact resolve b2e116 b2e4907
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116 b2e4907
        have b2e4993 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e4940
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e4940
          | exact resolve b2e4940 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4940
        have b2e5045 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e17 y y
             have i₂ := b2e4993
             grind)
          | exact superpose b2e4993 b2e17
          | (have j0 := b2e17 y y
             grind)
          | exact resolve b2e17 b2e4993
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4993
        have b2e5058 : y = (M.op y y) ∨ x = y := by grind
        clear b2e5045
        have b2e5084 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e5058
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5058
          | exact resolve b2e5058 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5058
        have b2e5085 : x = y := by grind
        clear b2e5084
        have b2e5280 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e5085
             grind)
          | exact superpose b2e5085 b2e22
          | exact resolve b2e22 b2e5085
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5295 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e782
             have i₂ := b2e5085
             grind)
          | exact superpose b2e5085 b2e782
          | exact resolve b2e782 b2e5085
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e782 b2e5085
        have b2e5302 : False := by grind
        exact b2e5302
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b3e26 : (σ y) = (k (σ x) (σ y)) := by grind
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
        have b3e33 : (k x y) = (τ (σ y)) := by
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
        have b3e34 : y = (k x y) := by
          first
          | (have i₁ := b3e33
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e33
          | exact resolve b3e33 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e50 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e55 : x = (k x y) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e20
             grind)
          | exact resolve b3e50 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e59 : x = y := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e55
          | exact resolve b3e55 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e55
        have b3e65 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e19
          | exact resolve b3e19 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e21
          | exact resolve b3e21 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e65
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e65
          | exact resolve b3e65 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e66
        have b3e71 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e70
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e70
          | exact resolve b3e70 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e72 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e71
          | exact resolve b3e71 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e71
        have b3e73 : False := by grind
        exact b3e73
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
          have b4e31 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
          have b4e99 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e31 (σ x)
               grind)
            | exact superpose b4e31 b4e20
            | exact resolve b4e20 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e100 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e99
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e99
            | exact resolve b4e99 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e104 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e100
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e100
            | exact resolve b4e100 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e100
          have b4e105 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e104
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e104
            | exact resolve b4e104 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104
          have b4e106 : False := by grind
          exact b4e106
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e38 : x = (M.op y y) ∨ x = (k x y) := by grind
          have b5e47 : x = (k x y) := by
            first
            | (have r₁ := b5e38
               have r₂ := b5e21
               grind)
            | exact resolve b5e38 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e64 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ y) (σ x)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b5e86 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e14
            | exact resolve b5e14 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e112 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            grind
          clear b5e86
          have b5e118 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e112 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e112
            | exact resolve b5e112 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112
          have b5e920 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e64 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e921 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e920
               have r₂ := b5e24
               grind)
            | exact resolve b5e920 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e920
          have b5e922 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e921
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e921
            | exact resolve b5e921 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e921
          have b5e923 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e922
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e922
            | exact resolve b5e922 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e922
          have b5e926 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e923
               grind)
            | exact superpose b5e923 b5e20
            | exact resolve b5e20 b5e923
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e923
          have b5e929 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e926
               have i₂ := b5e28 x
               grind)
            | exact superpose b5e28 b5e926
            | exact resolve b5e926 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e926
          have b5e930 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e929
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e929
            | exact resolve b5e929 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e929
          have b5e2273 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e73 x x
               grind)
            | exact superpose b5e73 b5e24
            | (have j1 := b5e73 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e73 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e73 x y
               grind)
            | exact resolve b5e24 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e2438 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e2273
          have b5e4895 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e2438
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e2438
            | (have j1 := b5e18 (σ x) (σ x)
               grind)
            | exact resolve b5e2438 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2438
          have b5e4906 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e4895
          have b5e4923 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e4906
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4906
            | exact resolve b5e4906 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4906
          have b5e4924 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e4923
          have b5e4939 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e4924
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4924
            | exact resolve b5e4924 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4924
          have b5e5086 : x = (k (τ (σ x)) x) ∨ x = y := by
            first
            | (have i₁ := b5e118 x
               have i₂ := b5e4939
               grind)
            | exact superpose b5e4939 b5e118
            | exact resolve b5e118 b5e4939
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118 b5e4939
          have b5e5140 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e5086
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e5086
            | exact resolve b5e5086 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5086
          have b5e5296 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e5140
               grind)
            | exact superpose b5e5140 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e5140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5140
          have b5e5309 : x = (M.op x x) ∨ x = y := by grind
          clear b5e5296
          have b5e5339 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e5309
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e5309
            | exact resolve b5e5309 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5309
          have b5e5340 : x = y := by grind
          clear b5e5339
          have b5e5396 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e930
               have i₂ := b5e5340
               grind)
            | exact superpose b5e5340 b5e930
            | exact resolve b5e930 b5e5340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e930 b5e5340
          have b5e5399 : False := by grind
          exact b5e5399
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b6e25 : (σ y) = (k (σ x) (σ y)) := by grind
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
        have b6e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b6e96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b6e99 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e26
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e26 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e102 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e99
             have r₂ := b6e20
             grind)
          | exact resolve b6e99 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e111 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b6e102
             have r₂ := b6e21
             grind)
          | exact resolve b6e102 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102
        have b6e241 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e2087 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e96 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e96
          | exact resolve b6e96 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e2366 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e2087
        have b6e2473 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e2366
             grind)
          | exact superpose b6e2366 b6e13
          | exact resolve b6e13 b6e2366
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2493 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2473
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2473
          | exact resolve b6e2473 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2473
        have b6e2809 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e2493
             grind)
          | exact superpose b6e2493 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e2493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2493
        have b6e2816 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e2809
        have b6e2824 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2816
             have r₂ := b6e20
             grind)
          | exact resolve b6e2816 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2816
        have b6e3099 : y ≠ y ∨ y = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e241 y
             have i₂ := b6e2824
             grind)
          | exact superpose b6e2824 b6e241
          | (have r₁ := b6e241 y
             have r₂ := b6e2824
             grind)
          | exact resolve b6e241 b6e2824
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e241 b6e2824
        have b6e3100 : y = (k y y) ∨ (σ x) = (σ y) := by grind
        clear b6e3099
        have b6e3676 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2366
             have i₂ := b6e3100
             grind)
          | exact superpose b6e3100 b6e2366
          | exact resolve b6e2366 b6e3100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2366 b6e3100
        have b6e3691 : (σ x) = (σ y) := by grind
        clear b6e3676
        have b6e4130 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e3691
             grind)
          | exact superpose b6e3691 b6e19
          | exact resolve b6e19 b6e3691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4156 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4130
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4130
          | exact resolve b6e4130 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4130
        have b6e4163 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e4156
             have i₂ := b6e3691
             grind)
          | exact superpose b6e3691 b6e4156
          | exact resolve b6e4156 b6e3691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3691 b6e4156
        have b6e4170 : False := by grind
        exact b6e4170
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e29 (σ x)
               grind)
            | exact superpose b7e29 b7e20
            | exact resolve b7e20 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e45 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e44
            | exact resolve b7e44 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e47 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          have b7e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b7e56 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e23
               grind)
            | exact resolve b7e47 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e57 : (σ x) = (σ (k x y)) := by
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
          have b7e60 : (τ (σ x)) = (k x y) := by
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
          have b7e94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b7e116 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
          have b7e117 : x = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e116
               have r₂ := b7e21
               grind)
            | exact resolve b7e116 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116
          have b7e119 : x = (M.op x y) := by
            first
            | (have r₁ := b7e117
               have r₂ := b7e22
               grind)
            | exact resolve b7e117 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117
          have b7e169 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e119
               grind)
            | exact superpose b7e119 b7e45
            | exact resolve b7e45 b7e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45 b7e119
          have b7e216 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e53 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e2178 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
          have b7e2469 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e2178
          have b7e2539 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b7e2469
               have r₂ := b7e169
               grind)
            | exact resolve b7e2469 b7e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2469
          have b7e2587 : (τ (σ y)) = (k x x) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e2539
               grind)
            | exact superpose b7e2539 b7e14
            | exact resolve b7e14 b7e2539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2608 : y = (k x x) := by
            first
            | (have i₁ := b7e2587
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e2587
            | exact resolve b7e2587 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2587
          have b7e2936 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e2608
               grind)
            | exact superpose b7e2608 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e2608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2608
          have b7e2943 : y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e2936
          have b7e2951 : x = (M.op x x) := by
            first
            | (have r₁ := b7e2943
               have r₂ := b7e22
               grind)
            | exact resolve b7e2943 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2943
          have b7e3230 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b7e216 x
               have i₂ := b7e2951
               grind)
            | exact superpose b7e2951 b7e216
            | (have r₁ := b7e216 x
               have r₂ := b7e2951
               grind)
            | exact resolve b7e216 b7e2951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216 b7e2951
          have b7e3231 : x = (k x x) := by grind
          clear b7e3230
          have b7e3831 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2539
               have i₂ := b7e3231
               grind)
            | exact superpose b7e3231 b7e2539
            | exact resolve b7e2539 b7e3231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2539 b7e3231
          have b7e3857 : False := by grind
          exact b7e3857
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e66 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e842 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e66 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e843 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e842
               have r₂ := b8e24
               grind)
            | exact resolve b8e842 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e842
          have b8e844 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e843
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e843
            | exact resolve b8e843 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e843
          have b8e847 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e844
               grind)
            | exact superpose b8e844 b8e20
            | exact resolve b8e20 b8e844
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e844
          have b8e853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e847
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e847
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e847 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e847
          have b8e860 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e853
          have b8e864 : y = (M.op x x) := by
            first
            | (have r₁ := b8e860
               have r₂ := b8e21
               grind)
            | exact resolve b8e860 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e860
          have b8e866 : False := by grind
          exact b8e866

/-- `Equation326`: `x ◇ y = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_x_pyx_Equation326 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law326 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law326.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
        intro X0
        grind
      have b0e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
        intro X0
        grind
      have b0e68 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2
           have i₂ := b0e16 X0 X2
           grind)
        | (have i₁ := b0e11 X0 X1
           have i₂ := b0e16 (M.op X1 X1) X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X2
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e69 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e76 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        grind
      have b0e77 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op X1 X1) X1
           have i₂ := b0e16 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e11 X0 X1
           have i₂ := b0e16 X0 (M.op X0 (M.op X1 X1))
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X0 X0) X1
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e16 (σ X1) (σ X0)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e87 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X1) X0) ∨ (M.op (M.op X1 X1) X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e77 X0 X1
           have i₂ := b0e11 X0 X1
           grind)
        | exact superpose b0e11 b0e77
        | (have j0 := b0e77 X0 X1
           grind)
        | exact resolve b0e77 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e332 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = X1 ∨ (k X1 X0) = X0 := by
        intro X0 X1
        grind
      clear b0e69
      have b0e400 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e43 X0
           have i₂ := b0e76 X0 X1
           grind)
        | (have i₁ := b0e43 X0
           have i₂ := b0e76 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e76 b0e43
        | (have j1 := b0e76 X1 X0
           grind)
        | exact resolve b0e43 b0e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e422 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e400 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e400
      have b0e754 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) ∨ (M.op x x) = X1 ∨ (k x X1) = (M.op X1 x) := by
        intro X0 X1
        first
        | (have i₁ := b0e26 X0
           have i₂ := b0e68 x X0 X1
           grind)
        | (have i₁ := b0e26 X1
           have i₂ := b0e68 X0 X1 x
           grind)
        | exact superpose b0e68 b0e26
        | (have j1 := b0e68 x X1 X1
           grind)
        | exact resolve b0e26 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e847 : ∀ X0 X1 : G, (M.op x y) = X1 ∨ (M.op X0 X1) = (M.op X0 y) ∨ (k x X1) = (M.op X1 x) := by
        intro X0 X1
        first
        | (have i₁ := b0e754 X0 X1
           have i₂ := b0e26 x
           grind)
        | exact superpose b0e26 b0e754
        | (have j0 := b0e754 X0 X1
           grind)
        | exact resolve b0e754 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e754
      have b0e874 : ∀ X0 X1 : G, (k x X1) = (M.op X1 y) ∨ (M.op X0 X1) = (M.op X0 y) ∨ (M.op x y) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e847 X0 X1
           have i₂ := b0e26 X1
           grind)
        | exact superpose b0e26 b0e847
        | (have j0 := b0e847 X0 X1
           grind)
        | exact resolve b0e847 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e847
      have b0e1450 : ∀ X0 : G, (M.op X0 y) = (k x X0) ∨ (M.op X0 X0) = x ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e87 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e87
        | exact resolve b0e87 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1483 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) ∨ (M.op X0 X1) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X1
           have i₂ := b0e87 X0 X1
           grind)
        | (have i₁ := b0e29 X0
           have i₂ := b0e87 (M.op (M.op X0 X0) X0) X1
           grind)
        | exact superpose b0e87 b0e29
        | (have j1 := b0e87 X0 X1
           grind)
        | exact resolve b0e29 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e87
      have b0e2622 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e81 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e2623 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e2622 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2622
      have b0e6218 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e332 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e332
      have b0e6220 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e6218 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6218
      have b0e6331 : x ≠ (M.op x y) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e6220 x
           have i₂ := b0e26 x
           grind)
        | exact superpose b0e26 b0e6220
        | (have j0 := b0e6220 x
           grind)
        | exact resolve b0e6220 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e6220
      have b0e6625 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e422 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e422
      have b0e9695 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e6625 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6625
      have b0e9799 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e9695 (σ x)
           have i₂ := b0e17 x x
           grind)
        | exact superpose b0e17 b0e9695
        | exact resolve b0e9695 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9695
      have b0e13858 : ∀ X0 : G, x = (M.op X0 y) ∨ (M.op X0 y) = (k x X0) ∨ (M.op x y) = X0 ∨ (M.op X0 y) = (k x X0) ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1450 X0
           have i₂ := b0e874 X0 X0
           grind)
        | (have i₁ := b0e1450 y
           have i₂ := b0e874 y x
           grind)
        | exact superpose b0e874 b0e1450
        | (have j0 := b0e1450 X0
           have j1 := b0e874 X0 X0
           grind)
        | exact resolve b0e1450 b0e874
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e874 b0e1450
      have b0e13973 : ∀ X0 : G, (M.op X0 y) = (k x X0) ∨ x = (M.op X0 y) ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have j0 := b0e13858 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13858
      have b0e95244 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e27 (σ x)
           have i₂ := b0e9799 x
           grind)
        | exact superpose b0e9799 b0e27
        | (have j1 := b0e9799 x
           grind)
        | exact resolve b0e27 b0e9799
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9799
      have b0e95917 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (k X0 x) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b0e1483 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1483
        | exact resolve b0e1483 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1483
      have b0e128230 : ∀ X0 : G, x = (k X0 x) ∨ (k X0 x) = X0 ∨ x = (k X0 x) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b0e43 X0
           have i₂ := b0e95917 X0
           grind)
        | exact superpose b0e95917 b0e43
        | (have j1 := b0e95917 X0
           grind)
        | exact resolve b0e43 b0e95917
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e95917
      have b0e128310 : ∀ X0 : G, x = (k X0 x) ∨ (k X0 x) = X0 ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e128230 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128230
      have b0e144350 : ∀ X0 : G, x ≠ X0 ∨ (k X0 x) = X0 ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e128310 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128310
      have b0e145969 : (M.op x y) = (k x x) ∨ x = (k x x) := by
        first
        | (have j0 := b0e144350 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144350
      have b0e182779 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e95244
           grind)
        | exact superpose b0e95244 b0e18
        | exact resolve b0e18 b0e95244
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95244
      have b0e183274 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e182779
           have i₂ := b0e145969
           grind)
        | exact superpose b0e145969 b0e182779
        | exact resolve b0e182779 b0e145969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145969 b0e182779
      have b0e183281 : (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by grind
      clear b0e183274
      have b0e184113 : (M.op x y) = (τ (σ x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e183281
           grind)
        | exact superpose b0e183281 b0e12
        | exact resolve b0e12 b0e183281
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e183281
      have b0e184153 : x = (M.op x y) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e184113
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e184113
        | exact resolve b0e184113 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e184113
      have b0e184154 : x = (k x x) := by
        first
        | (have r₁ := b0e184153
           have r₂ := b0e6331
           grind)
        | exact resolve b0e184153 b0e6331
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6331 b0e184153
      have b0e185335 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e13973 x
           have i₂ := b0e184154
           grind)
        | exact superpose b0e184154 b0e13973
        | (have j0 := b0e13973 x
           grind)
        | exact resolve b0e13973 b0e184154
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13973
      have b0e185343 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e2623 x
           have i₂ := b0e184154
           grind)
        | exact superpose b0e184154 b0e2623
        | (have j0 := b0e2623 x
           grind)
        | exact resolve b0e2623 b0e184154
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2623 b0e184154
      have b0e185414 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e185343
      have b0e185419 : x = (M.op x y) := by grind
      clear b0e185335
      have b0e185493 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e185414
           have i₂ := b0e27 (σ x)
           grind)
        | exact superpose b0e27 b0e185414
        | exact resolve b0e185414 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e185414
      have b0e188457 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e185493
           grind)
        | exact superpose b0e185493 b0e18
        | exact resolve b0e18 b0e185493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e185493
      have b0e188588 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e188457
           have i₂ := b0e185419
           grind)
        | exact superpose b0e185419 b0e188457
        | exact resolve b0e188457 b0e185419
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e185419 b0e188457
      have b0e188589 : False := by grind
      exact b0e188589
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b1e25 : y = (k x y) := by grind
        have b1e46 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e53 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e21
             grind)
          | exact resolve b1e46 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e57 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e58 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e57
          | exact resolve b1e57 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e57
        have b1e59 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e19
          | exact resolve b1e19 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e22
          | exact resolve b1e22 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e13
          | exact resolve b1e13 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : x = y := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e63
          | exact resolve b1e63 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e67 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e59
          | exact resolve b1e59 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e60
        have b1e68 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e67
             have i₂ := b1e64
             grind)
          | exact superpose b1e64 b1e67
          | exact resolve b1e67 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e67
        have b1e69 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e68
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e68
          | exact resolve b1e68 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e70 : False := by grind
        exact b1e70
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : y = (k x y) := by grind
        have b2e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e53 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e33 X0 X1
             grind)
          | exact superpose b2e33 b2e13
          | exact resolve b2e13 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e72 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
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
        have b2e82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b2e112 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          grind
        clear b2e53
        have b2e118 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e112 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e112
          | exact resolve b2e112 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e112
        have b2e803 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e72 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72
        have b2e804 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e803
             have r₂ := b2e22
             grind)
          | exact resolve b2e803 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e803
        have b2e805 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e804
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e804
          | exact resolve b2e804 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e804
        have b2e806 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e805
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e805
          | exact resolve b2e805 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e805
        have b2e2129 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e82 y y
             grind)
          | exact superpose b2e82 b2e21
          | (have j1 := b2e82 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e82 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e82 x y
             grind)
          | exact resolve b2e21 b2e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e2282 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e2129
        have b2e4956 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e2282
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e2282
          | (have j1 := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e2282 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2282
        have b2e4967 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e4956
        have b2e4984 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e4967
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4967
          | exact resolve b2e4967 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4967
        have b2e4985 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e4984
        have b2e5000 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e4985
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4985
          | exact resolve b2e4985 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4985
        have b2e5042 : y = (k (τ (σ y)) y) ∨ x = y := by
          first
          | (have i₁ := b2e118 y
             have i₂ := b2e5000
             grind)
          | exact superpose b2e5000 b2e118
          | exact resolve b2e118 b2e5000
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e118 b2e5000
        have b2e5095 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e5042
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e5042
          | exact resolve b2e5042 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5042
        have b2e5360 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e17 y y
             have i₂ := b2e5095
             grind)
          | exact superpose b2e5095 b2e17
          | (have j0 := b2e17 y y
             grind)
          | exact resolve b2e17 b2e5095
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5095
        have b2e5373 : y = (M.op y y) ∨ x = y := by grind
        clear b2e5360
        have b2e5401 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e5373
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5373
          | exact resolve b2e5373 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5373
        have b2e5402 : x = y := by grind
        clear b2e5401
        have b2e5698 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e5402
             grind)
          | exact superpose b2e5402 b2e22
          | exact resolve b2e22 b2e5402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5713 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e806
             have i₂ := b2e5402
             grind)
          | exact superpose b2e5402 b2e806
          | exact resolve b2e806 b2e5402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e806 b2e5402
        have b2e5724 : False := by grind
        exact b2e5724
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b3e26 : (σ y) = (k (σ x) (σ y)) := by grind
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
        have b3e33 : (k x y) = (τ (σ y)) := by
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
        have b3e34 : y = (k x y) := by
          first
          | (have i₁ := b3e33
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e33
          | exact resolve b3e33 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e50 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e55 : x = (k x y) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e20
             grind)
          | exact resolve b3e50 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e59 : x = y := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e55
          | exact resolve b3e55 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e55
        have b3e65 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e19
          | exact resolve b3e19 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e21
          | exact resolve b3e21 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e65
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e65
          | exact resolve b3e65 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e66
        have b3e71 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e70
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e70
          | exact resolve b3e70 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e72 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e71
          | exact resolve b3e71 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e71
        have b3e73 : False := by grind
        exact b3e73
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
          have b4e31 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
          have b4e99 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e31 (σ x)
               grind)
            | exact superpose b4e31 b4e20
            | exact resolve b4e20 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e100 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e99
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e99
            | exact resolve b4e99 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e104 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e100
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e100
            | exact resolve b4e100 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e100
          have b4e105 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e104
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e104
            | exact resolve b4e104 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104
          have b4e106 : False := by grind
          exact b4e106
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
          have b5e27 : x = (k y x) := by grind
          have b5e28 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
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
          have b5e73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b5e86 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e14
            | exact resolve b5e14 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e112 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            grind
          clear b5e86
          have b5e118 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e112 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e112
            | exact resolve b5e112 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112
          have b5e938 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e65 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e939 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e938
               have r₂ := b5e23
               grind)
            | exact resolve b5e938 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e938
          have b5e940 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e939
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e939
            | exact resolve b5e939 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e939
          have b5e941 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e940
               have i₂ := b5e27
               grind)
            | exact superpose b5e27 b5e940
            | exact resolve b5e940 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e940
          have b5e944 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e941
               grind)
            | exact superpose b5e941 b5e20
            | exact resolve b5e20 b5e941
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e941
          have b5e947 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e944
               have i₂ := b5e28 x
               grind)
            | exact superpose b5e28 b5e944
            | exact resolve b5e944 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e944
          have b5e948 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e947
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e947
            | exact resolve b5e947 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e947
          have b5e2271 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e73 x x
               grind)
            | exact superpose b5e73 b5e24
            | (have j1 := b5e73 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e73 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e73 y x
               grind)
            | exact resolve b5e24 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e2436 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e2271
          have b5e4888 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e2436
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e2436
            | (have j1 := b5e18 (σ x) (σ x)
               grind)
            | exact resolve b5e2436 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2436
          have b5e4899 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e4888
          have b5e4916 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e4899
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4899
            | exact resolve b5e4899 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4899
          have b5e4917 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e4916
          have b5e4932 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e4917
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4917
            | exact resolve b5e4917 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4917
          have b5e5079 : x = (k (τ (σ x)) x) ∨ x = y := by
            first
            | (have i₁ := b5e118 x
               have i₂ := b5e4932
               grind)
            | exact superpose b5e4932 b5e118
            | exact resolve b5e118 b5e4932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118 b5e4932
          have b5e5133 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e5079
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e5079
            | exact resolve b5e5079 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5079
          have b5e5289 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e5133
               grind)
            | exact superpose b5e5133 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e5133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5133
          have b5e5302 : x = (M.op x x) ∨ x = y := by grind
          clear b5e5289
          have b5e5332 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e5302
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e5302
            | exact resolve b5e5302 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5302
          have b5e5333 : x = y := by grind
          clear b5e5332
          have b5e5389 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e948
               have i₂ := b5e5333
               grind)
            | exact superpose b5e5333 b5e948
            | exact resolve b5e948 b5e5333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e948 b5e5333
          have b5e5391 : False := by grind
          exact b5e5391
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b6e25 : (σ y) = (k (σ x) (σ y)) := by grind
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
        have b6e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b6e96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e99 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e26
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e26 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e102 : (σ y) = (σ (M.op y x)) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e99
             have r₂ := b6e20
             grind)
          | exact resolve b6e99 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e111 : (σ y) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e102
             have r₂ := b6e21
             grind)
          | exact resolve b6e102 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102
        have b6e247 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e1829 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e96 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e96
          | exact resolve b6e96 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e2098 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e1829
        have b6e3297 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e2098
             grind)
          | exact superpose b6e2098 b6e13
          | exact resolve b6e13 b6e2098
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3317 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3297
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3297
          | exact resolve b6e3297 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3297
        have b6e3643 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e3317
             grind)
          | exact superpose b6e3317 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e3317
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3317
        have b6e3656 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e3643
        have b6e3670 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3656
             have r₂ := b6e20
             grind)
          | exact resolve b6e3656 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3656
        have b6e3979 : y ≠ y ∨ y = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e247 y
             have i₂ := b6e3670
             grind)
          | exact superpose b6e3670 b6e247
          | (have r₁ := b6e247 y
             have r₂ := b6e3670
             grind)
          | exact resolve b6e247 b6e3670
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e247 b6e3670
        have b6e3980 : y = (k y y) ∨ (σ x) = (σ y) := by grind
        clear b6e3979
        have b6e4042 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2098
             have i₂ := b6e3980
             grind)
          | exact superpose b6e3980 b6e2098
          | exact resolve b6e2098 b6e3980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2098 b6e3980
        have b6e4057 : (σ x) = (σ y) := by grind
        clear b6e4042
        have b6e4184 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e4057
             grind)
          | exact superpose b6e4057 b6e19
          | exact resolve b6e19 b6e4057
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4190 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e4057
             grind)
          | exact superpose b6e4057 b6e13
          | exact resolve b6e13 b6e4057
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4214 : x = y := by
          first
          | (have i₁ := b6e4190
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e4190
          | exact resolve b6e4190 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4190
        have b6e4216 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4184
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4184
          | exact resolve b6e4184 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4184
        have b6e4223 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e4216
             have i₂ := b6e4057
             grind)
          | exact superpose b6e4057 b6e4216
          | exact resolve b6e4216 b6e4057
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4057 b6e4216
        have b6e4230 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e4223
             have i₂ := b6e4214
             grind)
          | exact superpose b6e4214 b6e4223
          | exact resolve b6e4223 b6e4214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4223
        have b6e4356 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e111
             have i₂ := b6e4214
             grind)
          | exact superpose b6e4214 b6e111
          | exact resolve b6e111 b6e4214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111 b6e4214
        have b6e4375 : False := by grind
        exact b6e4375
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : (σ x) = (k (σ y) (σ x)) := by grind
          have b7e28 : (σ x) = (σ (k y x)) := by
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
          have b7e29 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : (k y x) = (τ (σ x)) := by
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
          have b7e34 : x = (k y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e44 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e29 (σ x)
               grind)
            | exact superpose b7e29 b7e20
            | exact resolve b7e20 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e45 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e44
            | exact resolve b7e44 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b7e94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e96 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e101 : x = (M.op x y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e96
               have r₂ := b7e22
               grind)
            | exact resolve b7e96 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e112 : x = (M.op x y) := by
            first
            | (have r₁ := b7e101
               have r₂ := b7e21
               grind)
            | exact resolve b7e101 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e169 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e112
               grind)
            | exact superpose b7e112 b7e45
            | exact resolve b7e45 b7e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45 b7e112
          have b7e217 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e53 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e2177 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
          have b7e2468 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e2177
          have b7e2538 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b7e2468
               have r₂ := b7e169
               grind)
            | exact resolve b7e2468 b7e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2468
          have b7e2588 : (τ (σ y)) = (k x x) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e2538
               grind)
            | exact superpose b7e2538 b7e14
            | exact resolve b7e14 b7e2538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2609 : y = (k x x) := by
            first
            | (have i₁ := b7e2588
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e2588
            | exact resolve b7e2588 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2588
          have b7e2936 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e2609
               grind)
            | exact superpose b7e2609 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e2609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2609
          have b7e2943 : y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e2936
          have b7e2951 : x = (M.op x x) := by
            first
            | (have r₁ := b7e2943
               have r₂ := b7e22
               grind)
            | exact resolve b7e2943 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2943
          have b7e3244 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b7e217 x
               have i₂ := b7e2951
               grind)
            | exact superpose b7e2951 b7e217
            | (have r₁ := b7e217 x
               have r₂ := b7e2951
               grind)
            | exact resolve b7e217 b7e2951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e217 b7e2951
          have b7e3245 : x = (k x x) := by grind
          clear b7e3244
          have b7e3827 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2538
               have i₂ := b7e3245
               grind)
            | exact superpose b7e3245 b7e2538
            | exact resolve b7e2538 b7e3245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2538 b7e3245
          have b7e3853 : False := by grind
          exact b7e3853
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
          have b8e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
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
          have b8e856 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e67 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e857 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e856
               have r₂ := b8e23
               grind)
            | exact resolve b8e856 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e856
          have b8e858 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e857
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e857
            | exact resolve b8e857 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e857
          have b8e861 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e858
               grind)
            | exact superpose b8e858 b8e20
            | exact resolve b8e20 b8e858
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e858
          have b8e1065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e861
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e861
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e861 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e861
          have b8e1080 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e1065
          have b8e1089 : x = (M.op y y) := by
            first
            | (have r₁ := b8e1080
               have r₂ := b8e22
               grind)
            | exact resolve b8e1080 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1080
          have b8e1092 : False := by grind
          exact b8e1092

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_pyx_pxy_Equation327 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law327 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
      have b0e26 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
      have b0e42 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e26 (σ x)
           grind)
        | exact superpose b0e26 b0e18
        | exact resolve b0e18 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e43 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e42
        | exact resolve b0e42 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e45 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e25 x
           grind)
        | exact superpose b0e25 b0e43
        | exact resolve b0e43 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e43
      have b0e46 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e45
        | exact resolve b0e45 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e47 : False := by grind
      exact b0e47
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b1e101 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e32 X1 X0
             grind)
          | exact superpose b1e32 b1e13
          | exact resolve b1e13 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e238 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e101
        have b1e253 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e238 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e238
          | exact resolve b1e238 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e238
        have b1e455 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e64 x x
             grind)
          | exact superpose b1e64 b1e21
          | (have j1 := b1e64 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e64 x y
             grind)
          | exact resolve b1e21 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e510 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e455
        have b1e1030 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e510
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e510
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e510 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e510
        have b1e1031 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1030
        have b1e1032 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1031
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1031
          | exact resolve b1e1031 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1031
        have b1e1033 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1032
        have b1e1039 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1033
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1033
          | exact resolve b1e1033 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1033
        have b1e1094 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e253 x
             have i₂ := b1e1039
             grind)
          | exact superpose b1e1039 b1e253
          | exact resolve b1e253 b1e1039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e253 b1e1039
        have b1e1107 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e1094
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1094
          | exact resolve b1e1094 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1094
        have b1e1182 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e1107
             grind)
          | exact superpose b1e1107 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e1107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1107
        have b1e1183 : x = (M.op x x) ∨ x = y := by grind
        clear b1e1182
        have b1e1192 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1183
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1183
          | exact resolve b1e1183 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1183
        have b1e1193 : x = y := by grind
        clear b1e1192
        have b1e1230 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1193
             grind)
          | exact superpose b1e1193 b1e22
          | exact resolve b1e22 b1e1193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1488 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1230
             grind)
          | exact superpose b1e1230 b1e21
          | exact resolve b1e21 b1e1230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230
        have b1e1506 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e1488
             have i₂ := b1e1193
             grind)
          | exact superpose b1e1193 b1e1488
          | exact resolve b1e1488 b1e1193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1193 b1e1488
        have b1e1507 : False := by grind
        exact b1e1507
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
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
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e31 X1 X0
             grind)
          | exact superpose b2e31 b2e13
          | exact resolve b2e13 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b2e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
        have b2e116 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e48
        have b2e130 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e116 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e116
          | exact resolve b2e116 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116
        have b2e214 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e65 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e215 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e214
             have r₂ := b2e22
             grind)
          | exact resolve b2e214 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e214
        have b2e216 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e215
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e215
          | exact resolve b2e215 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e215
        have b2e217 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e216
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e216
          | exact resolve b2e216 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e216
        have b2e220 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e217
             grind)
          | exact superpose b2e217 b2e19
          | exact resolve b2e19 b2e217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e217
        have b2e226 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e220
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e220
          | exact resolve b2e220 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e220
        have b2e227 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e226
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e226
          | exact resolve b2e226 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e226
        have b2e355 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e57 x x
             grind)
          | exact superpose b2e57 b2e21
          | (have j1 := b2e57 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e57 x y
             grind)
          | exact resolve b2e21 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e409 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e355
        have b2e909 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e409
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e409
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e409 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e409
        have b2e910 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e909
        have b2e911 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e910
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e910
          | exact resolve b2e910 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e910
        have b2e912 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e911
        have b2e918 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e912
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e912
          | exact resolve b2e912 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e912
        have b2e931 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e130 x
             have i₂ := b2e918
             grind)
          | exact superpose b2e918 b2e130
          | exact resolve b2e130 b2e918
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130 b2e918
        have b2e943 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e931
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e931
          | exact resolve b2e931 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e931
        have b2e981 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e943
             grind)
          | exact superpose b2e943 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e943
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e943
        have b2e982 : x = (M.op x x) ∨ x = y := by grind
        clear b2e981
        have b2e991 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e982
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e982
          | exact resolve b2e982 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e982
        have b2e992 : x = y := by grind
        clear b2e991
        have b2e1027 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e227
             have i₂ := b2e992
             grind)
          | exact superpose b2e992 b2e227
          | exact resolve b2e227 b2e992
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e227 b2e992
        have b2e1028 : False := by grind
        exact b2e1028
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
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
        have b3e29 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
        have b3e49 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e29 (σ x)
             grind)
          | exact superpose b3e29 b3e19
          | exact resolve b3e19 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e54 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e49
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e49
          | exact resolve b3e49 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e55 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e28 x
             grind)
          | exact superpose b3e28 b3e54
          | exact resolve b3e54 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e54
        have b3e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b3e452 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e63 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e63
          | exact resolve b3e63 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e520 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e452
        have b3e684 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e520
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e520
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e520 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e696 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e684
        have b3e708 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e696
             have r₂ := b3e55
             grind)
          | exact resolve b3e696 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e696
        have b3e783 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e708
        have b3e893 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e520
             have i₂ := b3e783
             grind)
          | exact superpose b3e783 b3e520
          | exact resolve b3e520 b3e783
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e520 b3e783
        have b3e900 : (σ x) = (σ y) := by grind
        clear b3e893
        have b3e970 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e900
             grind)
          | exact superpose b3e900 b3e13
          | exact resolve b3e13 b3e900
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1001 : x = y := by
          first
          | (have i₁ := b3e970
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e970
          | exact resolve b3e970 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e970
        have b3e1087 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1001
             grind)
          | exact superpose b3e1001 b3e19
          | exact resolve b3e19 b3e1001
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1088 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1001
             grind)
          | exact superpose b3e1001 b3e21
          | exact resolve b3e21 b3e1001
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1001
        have b3e1095 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1087
             have i₂ := b3e1088
             grind)
          | exact superpose b3e1088 b3e1087
          | exact resolve b3e1087 b3e1088
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1087 b3e1088
        have b3e1096 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1095
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1095
          | exact resolve b3e1095 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1095
        have b3e1097 : False := by grind
        exact b3e1097
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e35 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e27 (σ x)
               grind)
            | exact superpose b4e27 b4e20
            | exact resolve b4e20 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e39 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e35
               have i₂ := b4e26 x
               grind)
            | exact superpose b4e26 b4e35
            | exact resolve b4e35 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e35
          have b4e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b4e94 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e34 X1 X0
               grind)
            | exact superpose b4e34 b4e14
            | exact resolve b4e14 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e225 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b4e94
          have b4e240 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e225 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e225
            | exact resolve b4e225 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e225
          have b4e439 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e62 x x
               grind)
            | exact superpose b4e62 b4e39
            | (have j1 := b4e62 x x
               grind)
            | (have r₁ := b4e39
               have r₂ := b4e62 x (M.op x x)
               grind)
            | exact resolve b4e39 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e489 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e62 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e490 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e489 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e489
          have b4e497 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e439
          have b4e953 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e490 (τ X0)
               have i₂ := b4e34 X0 (τ X0)
               grind)
            | exact superpose b4e34 b4e490
            | (have j0 := b4e490 (τ X0)
               grind)
            | exact resolve b4e490 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e957 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e953 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e953
            | (have j0 := b4e953 X0
               grind)
            | exact resolve b4e953 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e953
          have b4e961 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e957 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e957
            | (have j0 := b4e957 X0
               grind)
            | exact resolve b4e957 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e957
          have b4e2841 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e497
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e497
            | (have j1 := b4e18 (σ x) (σ x)
               grind)
            | exact resolve b4e497 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e497
          have b4e2842 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e2841
          have b4e2843 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e2842
          have b4e2870 : x = (k x (τ (σ x))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e240 x
               have i₂ := b4e2843
               grind)
            | exact superpose b4e2843 b4e240
            | exact resolve b4e240 b4e2843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e240 b4e2843
          have b4e2887 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e2870
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e2870
            | exact resolve b4e2870 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2870
          have b4e2888 : x = (M.op x x) := by
            first
            | (have j1 := b4e961 x
               grind)
            | (have r₁ := b4e2887
               have r₂ := b4e961 x
               grind)
            | exact resolve b4e2887 b4e961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e961 b4e2887
          have b4e2935 : x = (k x x) := by grind
          have b4e3105 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e490 x
               have i₂ := b4e2935
               grind)
            | exact superpose b4e2935 b4e490
            | (have j0 := b4e490 x
               grind)
            | exact resolve b4e490 b4e2935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e490 b4e2935
          have b4e3122 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e3105
          have b4e3569 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e3122
               grind)
            | exact superpose b4e3122 b4e39
            | exact resolve b4e39 b4e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e3122
          have b4e3592 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e3569
               have i₂ := b4e2888
               grind)
            | exact superpose b4e2888 b4e3569
            | exact resolve b4e3569 b4e2888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2888 b4e3569
          have b4e3593 : False := by grind
          exact b4e3593
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e40 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          clear b5e40
          have b5e46 : x = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b5e59 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b5e74 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e33 X1 X0
               grind)
            | exact superpose b5e33 b5e14
            | exact resolve b5e14 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e159 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 X0 X2
               have i₂ := b5e59 X0 X0 X1
               grind)
            | (have i₁ := b5e18 X2 X1
               have i₂ := b5e59 X0 X2 X2
               grind)
            | exact superpose b5e59 b5e18
            | (have j0 := b5e18 X1 X0
               have j1 := b5e59 X0 X1 X1
               grind)
            | exact resolve b5e18 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e205 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e206 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e205
               have r₂ := b5e24
               grind)
            | exact resolve b5e205 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e205
          have b5e207 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e206
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e206
            | exact resolve b5e206 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e206
          have b5e208 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e207
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e207
            | exact resolve b5e207 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e207
          have b5e211 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e208
               grind)
            | exact superpose b5e208 b5e20
            | exact resolve b5e20 b5e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e217 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e211
               have i₂ := b5e26 x
               grind)
            | exact superpose b5e26 b5e211
            | exact resolve b5e211 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e211
          have b5e380 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e53 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e53 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e53 X0 X1
               grind)
            | exact resolve b5e17 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e392 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e380 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e380
          have b5e393 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e392 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e392
          have b5e403 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e393 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e393
            | (have j0 := b5e393 X0 X1
               grind)
            | exact resolve b5e393 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e393
          have b5e6010 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b5e403
          have b5e6050 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e6010 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e6010
            | (have j0 := b5e6010 X0 X1
               grind)
            | exact resolve b5e6010 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6010
          have b5e6051 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e6050 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6050
          have b5e7603 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e6051 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e6051
            | exact resolve b5e6051 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7727 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7603 X0 X1
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e7603
            | (have j0 := b5e7603 X0 X1
               grind)
            | exact resolve b5e7603 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7603
          have b5e7733 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7727 X0 X1
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e7727
            | (have j0 := b5e7727 X0 X1
               grind)
            | exact resolve b5e7727 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e7727
          have b5e9455 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e7733 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e7733
            | exact resolve b5e7733 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7733
          have b5e9707 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e9455 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9455
          have b5e10110 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e159 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e159
          have b5e10112 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e10110 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10110
          have b5e10113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e10112 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10112
          have b5e10328 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e9707 X0 (M.op X1 X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e9707
            | (have j0 := b5e9707 X0 X1
               grind)
            | exact resolve b5e9707 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9707
          have b5e11809 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e10328 (σ x) (σ y) X0
               have i₂ := b5e208
               grind)
            | exact superpose b5e208 b5e10328
            | (have j0 := b5e10328 (σ x) (σ y) X0
               grind)
            | (have r₁ := b5e10328 (σ x) (σ y) x
               have r₂ := b5e208
               grind)
            | exact resolve b5e10328 b5e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10328
          have b5e11829 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have j0 := b5e11809 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11809
          have b5e12879 : ∀ X0 : G, (k x (τ (M.op (σ y) X0))) = (τ (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e74 x (M.op (σ y) X0)
               have i₂ := b5e11829 X0
               grind)
            | exact superpose b5e11829 b5e74
            | exact resolve b5e74 b5e11829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74 b5e11829
          have b5e12909 : ∀ X0 : G, x = (k x (τ (M.op (σ y) X0))) := by
            intro X0
            first
            | (have i₁ := b5e12879 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e12879
            | exact resolve b5e12879 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12879
          have b5e13591 : ∀ X0 : G, x = (k x (τ (σ (k y X0)))) ∨ (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b5e12909 (σ X0)
               have i₂ := b5e6051 X0 y
               grind)
            | exact superpose b5e6051 b5e12909
            | (have j1 := b5e6051 X0 y
               grind)
            | exact resolve b5e12909 b5e6051
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6051 b5e12909
          have b5e13639 : ∀ X0 : G, x = (k x (k y X0)) ∨ (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b5e13591 X0
               have i₂ := b5e14 (k y X0)
               grind)
            | exact superpose b5e14 b5e13591
            | (have j0 := b5e13591 X0
               grind)
            | exact resolve b5e13591 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13591
          have b5e19674 : x = (k x (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e13639 y
               have i₂ := b5e10113 y
               grind)
            | exact superpose b5e10113 b5e13639
            | (have j1 := b5e10113 y
               grind)
            | exact resolve b5e13639 b5e10113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10113 b5e13639
          have b5e19750 : x = (k x (M.op y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e19674
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e19674
            | exact resolve b5e19674 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19674
          have b5e19768 : x = (k x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e19750
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e19750
            | exact resolve b5e19750 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19750
          have b5e19771 : (σ y) = (σ (M.op y x)) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e19768
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e19768
            | exact resolve b5e19768 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19768
          have b5e19772 : (σ x) = (σ y) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e19771
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e19771
            | exact resolve b5e19771 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19771
          have b5e19773 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e19772
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e19772
            | exact resolve b5e19772 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e19772
          have b5e19774 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e19773
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e19773
            | exact resolve b5e19773 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19773
          have b5e20886 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e19774
               grind)
            | exact superpose b5e19774 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e19774
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19774
          have b5e20917 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
          clear b5e20886
          have b5e21092 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e217
               have i₂ := b5e20917
               grind)
            | exact superpose b5e20917 b5e217
            | exact resolve b5e217 b5e20917
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e217 b5e20917
          have b5e21138 : (σ x) = (σ y) ∨ x = y := by grind
          clear b5e21092
          have b5e21298 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e21138
               grind)
            | exact superpose b5e21138 b5e14
            | exact resolve b5e14 b5e21138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21138
          have b5e21395 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e21298
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e21298
            | exact resolve b5e21298 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21298
          have b5e21396 : x = y := by grind
          clear b5e21395
          have b5e21403 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e21396
               grind)
            | exact superpose b5e21396 b5e24
            | exact resolve b5e24 b5e21396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e21412 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e208
               have i₂ := b5e21396
               grind)
            | exact superpose b5e21396 b5e208
            | exact resolve b5e208 b5e21396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e208 b5e21396
          have b5e21430 : False := by grind
          exact b5e21430
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
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
        have b6e26 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e25
             grind)
          | exact superpose b6e25 b6e13
          | exact resolve b6e13 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : x = (k x y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e28 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
        have b6e39 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e28 (σ x)
             grind)
          | exact superpose b6e28 b6e19
          | exact resolve b6e19 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e40 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e39
          | exact resolve b6e39 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b6e60 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e27
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e27 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e71 : x = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e20
             grind)
          | exact resolve b6e60 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e76 : x = (M.op x y) := by
          first
          | (have r₁ := b6e71
             have r₂ := b6e21
             grind)
          | exact resolve b6e71 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e78 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e76
             grind)
          | exact superpose b6e76 b6e40
          | exact resolve b6e40 b6e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e76
        have b6e417 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e58 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e58
          | exact resolve b6e58 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e484 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b6e417
        have b6e503 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e484
             have r₂ := b6e78
             grind)
          | exact resolve b6e484 b6e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e484
        have b6e540 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e503
             grind)
          | exact superpose b6e503 b6e13
          | exact resolve b6e13 b6e503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e562 : y = (k x x) := by
          first
          | (have i₁ := b6e540
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e540
          | exact resolve b6e540 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e540
        have b6e634 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e562
             grind)
          | exact superpose b6e562 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e562
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e562
        have b6e635 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e634
        have b6e637 : x = (M.op x x) := by
          first
          | (have r₁ := b6e635
             have r₂ := b6e20
             grind)
          | exact resolve b6e635 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e635
        have b6e674 : x = (k x x) := by grind
        clear b6e637
        have b6e792 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e503
             have i₂ := b6e674
             grind)
          | exact superpose b6e674 b6e503
          | exact resolve b6e503 b6e674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e503 b6e674
        have b6e803 : False := by grind
        exact b6e803
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e45 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e48 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e50 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e53 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e14
            | exact resolve b7e14 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : x = (k x y) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e53
            | exact resolve b7e53 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b7e81 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e82 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e81
               have r₂ := b7e21
               grind)
            | exact resolve b7e81 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e84 : x = (M.op x y) := by
            first
            | (have r₁ := b7e82
               have r₂ := b7e22
               grind)
            | exact resolve b7e82 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e492 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e26 (σ X0)
               have i₂ := b7e62 y X0
               grind)
            | exact superpose b7e62 b7e26
            | (have j1 := b7e62 y X0
               grind)
            | exact resolve b7e26 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e519 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e492 X0
               have i₂ := b7e26 (σ y)
               grind)
            | exact superpose b7e26 b7e492
            | (have j0 := b7e492 X0
               grind)
            | exact resolve b7e492 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e492
          have b7e561 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b7e519 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e519
            | (have j0 := b7e519 X0
               grind)
            | exact resolve b7e519 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e519
          have b7e3386 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e26 (σ y)
               have i₂ := b7e561 y
               grind)
            | exact superpose b7e561 b7e26
            | (have j1 := b7e561 y
               grind)
            | exact resolve b7e26 b7e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e561
          have b7e3448 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3386
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e3386
            | exact resolve b7e3386 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3386
          have b7e3479 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3448
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e3448
            | exact resolve b7e3448 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3448
          have b7e3480 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e3479
          have b7e3501 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e3480
               grind)
            | exact superpose b7e3480 b7e14
            | exact resolve b7e14 b7e3480
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3544 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3501
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e3501
            | exact resolve b7e3501 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3501
          have b7e3712 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e3544
               grind)
            | exact superpose b7e3544 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e3544
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3544
          have b7e3713 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3712
          have b7e4400 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3713
          have b7e4927 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3480
               have i₂ := b7e4400
               grind)
            | exact superpose b7e4400 b7e3480
            | exact resolve b7e3480 b7e4400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3480 b7e4400
          have b7e4946 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e4927
          have b7e5054 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y y
               have i₂ := b7e4946
               grind)
            | exact superpose b7e4946 b7e13
            | exact resolve b7e13 b7e4946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6127 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e4946
               have i₂ := b7e5054 y
               grind)
            | exact superpose b7e5054 b7e4946
            | exact resolve b7e4946 b7e5054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4946 b7e5054
          have b7e6170 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
          clear b7e6127
          have b7e6175 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e6170
               have r₂ := b7e22
               grind)
            | exact resolve b7e6170 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6170
          have b7e6787 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e6175
               grind)
            | exact superpose b7e6175 b7e14
            | exact resolve b7e14 b7e6175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6175
          have b7e6845 : x = y := by
            first
            | (have i₁ := b7e6787
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e6787
            | exact resolve b7e6787 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6787
          have b7e7328 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e6845
               grind)
            | exact superpose b7e6845 b7e22
            | exact resolve b7e22 b7e6845
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7338 : x = (M.op x x) := by
            first
            | (have i₁ := b7e84
               have i₂ := b7e6845
               grind)
            | exact superpose b7e6845 b7e84
            | exact resolve b7e84 b7e6845
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84 b7e6845
          have b7e7347 : False := by grind
          exact b7e7347
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b8e184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e185 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e184
               have r₂ := b8e24
               grind)
            | exact resolve b8e184 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e186 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e185
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e185
            | exact resolve b8e185 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185
          have b8e189 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e186
               grind)
            | exact superpose b8e186 b8e20
            | exact resolve b8e20 b8e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e189
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e189
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e189 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e189
          have b8e211 : y = (M.op x x) ∨ x = (M.op y x) := by grind
          clear b8e210
          have b8e214 : x = (M.op y x) := by
            first
            | (have r₁ := b8e211
               have r₂ := b8e21
               grind)
            | exact resolve b8e211 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211
          have b8e217 : False := by grind
          exact b8e217

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_pyy_pxy_Equation327 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law327 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
      have b0e26 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
      have b0e42 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e26 (σ x)
           grind)
        | exact superpose b0e26 b0e18
        | exact resolve b0e18 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e43 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e42
        | exact resolve b0e42 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e45 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e25 x
           grind)
        | exact superpose b0e25 b0e43
        | exact resolve b0e43 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e43
      have b0e46 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e45
        | exact resolve b0e45 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e47 : False := by grind
      exact b0e47
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b1e103 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e32 X1 X0
             grind)
          | exact superpose b1e32 b1e13
          | exact resolve b1e13 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e240 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e103
        have b1e255 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e240 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e240
          | exact resolve b1e240 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e240
        have b1e459 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e66 x x
             grind)
          | exact superpose b1e66 b1e21
          | (have j1 := b1e66 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e66 x y
             grind)
          | exact resolve b1e21 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e514 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e459
        have b1e1034 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e514
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e514
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e514 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e514
        have b1e1035 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1034
        have b1e1036 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1035
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1035
          | exact resolve b1e1035 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1035
        have b1e1037 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1036
        have b1e1043 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1037
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1037
          | exact resolve b1e1037 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1037
        have b1e1098 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e255 x
             have i₂ := b1e1043
             grind)
          | exact superpose b1e1043 b1e255
          | exact resolve b1e255 b1e1043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e255 b1e1043
        have b1e1111 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e1098
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1098
          | exact resolve b1e1098 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1098
        have b1e1186 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e1111
             grind)
          | exact superpose b1e1111 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e1111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1111
        have b1e1187 : x = (M.op x x) ∨ x = y := by grind
        clear b1e1186
        have b1e1196 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1187
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1187
          | exact resolve b1e1187 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1187
        have b1e1197 : x = y := by grind
        clear b1e1196
        have b1e1234 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1197
             grind)
          | exact superpose b1e1197 b1e22
          | exact resolve b1e22 b1e1197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1464 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1234
             grind)
          | exact superpose b1e1234 b1e21
          | exact resolve b1e21 b1e1234
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1234
        have b1e1482 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e1464
             have i₂ := b1e1197
             grind)
          | exact superpose b1e1197 b1e1464
          | exact resolve b1e1464 b1e1197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1197 b1e1464
        have b1e1483 : False := by grind
        exact b1e1483
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
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
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e31 X1 X0
             grind)
          | exact superpose b2e31 b2e13
          | exact resolve b2e13 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b2e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
        have b2e116 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e48
        have b2e130 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e116 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e116
          | exact resolve b2e116 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116
        have b2e214 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e65 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e215 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e214
             have r₂ := b2e22
             grind)
          | exact resolve b2e214 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e214
        have b2e216 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e215
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e215
          | exact resolve b2e215 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e215
        have b2e217 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e216
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e216
          | exact resolve b2e216 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e216
        have b2e220 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e217
             grind)
          | exact superpose b2e217 b2e19
          | exact resolve b2e19 b2e217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e217
        have b2e226 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e220
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e220
          | exact resolve b2e220 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e220
        have b2e227 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e226
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e226
          | exact resolve b2e226 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e226
        have b2e356 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e57 x x
             grind)
          | exact superpose b2e57 b2e21
          | (have j1 := b2e57 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e57 x y
             grind)
          | exact resolve b2e21 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e410 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e356
        have b2e910 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e410
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e410
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e410 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e410
        have b2e911 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e910
        have b2e912 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e911
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e911
          | exact resolve b2e911 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e911
        have b2e913 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e912
        have b2e919 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e913
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e913
          | exact resolve b2e913 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e913
        have b2e932 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e130 x
             have i₂ := b2e919
             grind)
          | exact superpose b2e919 b2e130
          | exact resolve b2e130 b2e919
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130 b2e919
        have b2e944 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e932
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e932
          | exact resolve b2e932 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e932
        have b2e982 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e944
             grind)
          | exact superpose b2e944 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e944
        have b2e983 : x = (M.op x x) ∨ x = y := by grind
        clear b2e982
        have b2e992 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e983
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e983
          | exact resolve b2e983 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e983
        have b2e993 : x = y := by grind
        clear b2e992
        have b2e1028 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e227
             have i₂ := b2e993
             grind)
          | exact superpose b2e993 b2e227
          | exact resolve b2e227 b2e993
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e227 b2e993
        have b2e1029 : False := by grind
        exact b2e1029
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
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
        have b3e29 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
        have b3e52 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e29 (σ x)
             grind)
          | exact superpose b3e29 b3e19
          | exact resolve b3e19 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e57 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e52
          | exact resolve b3e52 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e58 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e57
             have i₂ := b3e28 x
             grind)
          | exact superpose b3e28 b3e57
          | exact resolve b3e57 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e57
        have b3e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b3e457 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e66 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e66
          | exact resolve b3e66 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e525 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e457
        have b3e689 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e525
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e525
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e525 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e701 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e689
        have b3e713 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e701
             have r₂ := b3e58
             grind)
          | exact resolve b3e701 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58 b3e701
        have b3e788 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e713
        have b3e898 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e525
             have i₂ := b3e788
             grind)
          | exact superpose b3e788 b3e525
          | exact resolve b3e525 b3e788
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e525 b3e788
        have b3e905 : (σ x) = (σ y) := by grind
        clear b3e898
        have b3e975 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e905
             grind)
          | exact superpose b3e905 b3e13
          | exact resolve b3e13 b3e905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1006 : x = y := by
          first
          | (have i₁ := b3e975
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e975
          | exact resolve b3e975 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e975
        have b3e1092 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1006
             grind)
          | exact superpose b3e1006 b3e19
          | exact resolve b3e19 b3e1006
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1093 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1006
             grind)
          | exact superpose b3e1006 b3e21
          | exact resolve b3e21 b3e1006
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1006
        have b3e1100 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1092
             have i₂ := b3e1093
             grind)
          | exact superpose b3e1093 b3e1092
          | exact resolve b3e1092 b3e1093
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1092 b3e1093
        have b3e1101 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1100
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1100
          | exact resolve b3e1100 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1100
        have b3e1102 : False := by grind
        exact b3e1102
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e35 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e27 (σ x)
               grind)
            | exact superpose b4e27 b4e20
            | exact resolve b4e20 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e39 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e35
               have i₂ := b4e26 x
               grind)
            | exact superpose b4e26 b4e35
            | exact resolve b4e35 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e35
          have b4e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b4e98 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e34 X1 X0
               grind)
            | exact superpose b4e34 b4e14
            | exact resolve b4e14 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e229 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b4e98
          have b4e244 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e229 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e229
            | exact resolve b4e229 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229
          have b4e446 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e66 x x
               grind)
            | exact superpose b4e66 b4e39
            | (have j1 := b4e66 x x
               grind)
            | (have r₁ := b4e39
               have r₂ := b4e66 x (M.op x x)
               grind)
            | exact resolve b4e39 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e496 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e66 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e497 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e496 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e496
          have b4e504 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e446
          have b4e960 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e497 (τ X0)
               have i₂ := b4e34 X0 (τ X0)
               grind)
            | exact superpose b4e34 b4e497
            | (have j0 := b4e497 (τ X0)
               grind)
            | exact resolve b4e497 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e964 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e960 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e960
            | (have j0 := b4e960 X0
               grind)
            | exact resolve b4e960 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e960
          have b4e968 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e964 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e964
            | (have j0 := b4e964 X0
               grind)
            | exact resolve b4e964 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e964
          have b4e2849 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e504
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e504
            | (have j1 := b4e18 (σ x) (σ x)
               grind)
            | exact resolve b4e504 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e504
          have b4e2850 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e2849
          have b4e2851 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e2850
          have b4e2878 : x = (k x (τ (σ x))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e244 x
               have i₂ := b4e2851
               grind)
            | exact superpose b4e2851 b4e244
            | exact resolve b4e244 b4e2851
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e244 b4e2851
          have b4e2895 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e2878
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e2878
            | exact resolve b4e2878 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2878
          have b4e2896 : x = (M.op x x) := by
            first
            | (have j1 := b4e968 x
               grind)
            | (have r₁ := b4e2895
               have r₂ := b4e968 x
               grind)
            | exact resolve b4e2895 b4e968
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e968 b4e2895
          have b4e2943 : x = (k x x) := by grind
          have b4e3113 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e497 x
               have i₂ := b4e2943
               grind)
            | exact superpose b4e2943 b4e497
            | (have j0 := b4e497 x
               grind)
            | exact resolve b4e497 b4e2943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e497 b4e2943
          have b4e3130 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e3113
          have b4e3577 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e3130
               grind)
            | exact superpose b4e3130 b4e39
            | exact resolve b4e39 b4e3130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e3130
          have b4e3600 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e3577
               have i₂ := b4e2896
               grind)
            | exact superpose b4e2896 b4e3577
            | exact resolve b4e3577 b4e2896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2896 b4e3577
          have b4e3601 : False := by grind
          exact b4e3601
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X0)) := by
            intro X0 X1
            grind
          have b5e29 : y = (k y (M.op y x)) := by grind
          have b5e31 : y = (k y x) := by
            first
            | (have i₁ := b5e29
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e29
            | exact resolve b5e29 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e38 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e14
            | exact resolve b5e14 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e40 : x ≠ x ∨ y = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
          have b5e43 : y = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e40
          have b5e46 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e48 : (M.op y x) = (k x y) := by
            first
            | (have i₁ := b5e46
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e46
            | exact resolve b5e46 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e49 : x = (k x y) := by
            first
            | (have i₁ := b5e48
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e48
            | exact resolve b5e48 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b5e61 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b5e76 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e33 X1 X0
               grind)
            | exact superpose b5e33 b5e14
            | exact resolve b5e14 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e88 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e38 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e38
            | exact resolve b5e38 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e149 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 X0 X2
               have i₂ := b5e61 X1 X0 X0
               grind)
            | (have i₁ := b5e18 X0 X1
               have i₂ := b5e61 X0 X0 X2
               grind)
            | exact superpose b5e61 b5e18
            | (have j0 := b5e18 X0 X2
               have j1 := b5e61 X2 X1 X0
               grind)
            | exact resolve b5e18 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e188 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e76
          have b5e203 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e188 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e188
            | exact resolve b5e188 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e188
          have b5e207 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e208 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e207
               have r₂ := b5e24
               grind)
            | exact resolve b5e207 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e207
          have b5e209 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e208
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e208
            | exact resolve b5e208 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e208
          have b5e210 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e209
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e209
            | exact resolve b5e209 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e209
          have b5e213 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e210
               grind)
            | exact superpose b5e210 b5e20
            | exact resolve b5e20 b5e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e217 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b5e17 (σ y) (σ x)
               have i₂ := b5e210
               grind)
            | exact superpose b5e210 b5e17
            | (have j0 := b5e17 (σ y) (σ x)
               grind)
            | exact resolve b5e17 b5e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e218 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e217
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e217
            | exact resolve b5e217 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e217
          have b5e219 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e213
               have i₂ := b5e26 x
               grind)
            | exact superpose b5e26 b5e213
            | exact resolve b5e213 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213
          have b5e220 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e218
               have i₂ := b5e31
               grind)
            | exact superpose b5e31 b5e218
            | exact resolve b5e218 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e218
          have b5e221 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b5e220
               have r₂ := b5e23
               grind)
            | exact resolve b5e220 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e220
          have b5e355 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ (k X0 X1)) (M.op (σ (k X0 X1)) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e28 (σ X0) (σ X1)
               have i₂ := b5e55 X0 X1
               grind)
            | exact superpose b5e55 b5e28
            | (have j1 := b5e55 X0 X1
               grind)
            | exact resolve b5e28 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e385 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e55 X0 X1
               grind)
            | exact superpose b5e55 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e55 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e55 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e55 X0 X1
               grind)
            | exact resolve b5e17 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e397 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e385 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e385
          have b5e398 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e397 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e397
          have b5e408 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e398 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e398
            | (have j0 := b5e398 X0 X1
               grind)
            | exact resolve b5e398 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e398
          have b5e8410 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e408 (τ X1) (τ X0)
               have i₂ := b5e88 X0 X1
               grind)
            | exact superpose b5e88 b5e408
            | (have j0 := b5e408 (τ X1) (τ (k X0 X1))
               grind)
            | exact resolve b5e408 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88 b5e408
          have b5e9064 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e8410 X0 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e8410
            | (have j0 := b5e8410 X0 X1
               grind)
            | exact resolve b5e8410 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8410
          have b5e9143 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e9064 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e9064
            | (have j0 := b5e9064 X0 X1
               grind)
            | exact resolve b5e9064 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9064
          have b5e9157 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e9143 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e9143
            | (have j0 := b5e9143 X0 X1
               grind)
            | exact resolve b5e9143 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9143
          have b5e9162 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e9157 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e9157
            | (have j0 := b5e9157 X0 X1
               grind)
            | exact resolve b5e9157 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9157
          have b5e9163 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e9162 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e9162
            | (have j0 := b5e9162 X0 X1
               grind)
            | exact resolve b5e9162 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9162
          have b5e9164 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e9163 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e9163
            | (have j0 := b5e9163 X0 X1
               grind)
            | exact resolve b5e9163 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9163
          have b5e9165 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e9164 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e9164
            | (have j0 := b5e9164 X0 X1
               grind)
            | exact resolve b5e9164 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9164
          have b5e9702 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e149 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149
          have b5e9704 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e9702 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9702
          have b5e9705 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e9704 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9704
          have b5e67551 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e9165 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9165
          have b5e72315 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 y) ∨ (M.op X0 X0) = y ∨ (M.op y x) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e67551 X0 y
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e67551
            | (have j0 := b5e67551 X0 y
               grind)
            | exact resolve b5e67551 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67551
          have b5e72318 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = y ∨ (M.op y x) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e72315 X0
               have i₂ := b5e26 X0
               grind)
            | exact superpose b5e26 b5e72315
            | (have j0 := b5e72315 X0
               grind)
            | (have r₁ := b5e72315 y
               have r₂ := b5e26 y
               grind)
            | exact resolve b5e72315 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72315
          have b5e72322 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (M.op X0 X0) = y ∨ (M.op y x) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e72318 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e72318
            | (have j0 := b5e72318 X0
               grind)
            | exact resolve b5e72318 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72318
          have b5e72324 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k X0 y) ∨ (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b5e72322 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e72322
            | (have j0 := b5e72322 X0
               grind)
            | (have r₁ := b5e72322 y
               have r₂ := b5e22
               grind)
            | exact resolve b5e72322 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72322
          have b5e72347 : x ≠ x ∨ x = (k y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e72324 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e72324
            | (have j0 := b5e72324 y
               grind)
            | (have r₁ := b5e72324 y
               have r₂ := b5e22
               grind)
            | exact resolve b5e72324 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72324
          have b5e72348 : x = (k y y) ∨ y = (M.op y y) := by grind
          clear b5e72347
          have b5e72349 : y = (M.op y x) ∨ x = (k y y) := by
            first
            | (have i₁ := b5e72348
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e72348
            | exact resolve b5e72348 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e72348
          have b5e72350 : x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e72349
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e72349
            | exact resolve b5e72349 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72349
          have b5e72507 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e355 y y
               have i₂ := b5e72350
               grind)
            | exact superpose b5e72350 b5e355
            | (have j0 := b5e355 y y
               grind)
            | exact resolve b5e355 b5e72350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e355
          have b5e72542 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
          clear b5e72507
          have b5e72596 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e72542
               have i₂ := b5e210
               grind)
            | exact superpose b5e210 b5e72542
            | exact resolve b5e72542 b5e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e210 b5e72542
          have b5e72644 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
            first
            | (have i₁ := b5e72596
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e72596
            | exact resolve b5e72596 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72596
          have b5e72672 : y = (k y (τ (σ y))) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
            first
            | (have i₁ := b5e203 y
               have i₂ := b5e72644
               grind)
            | exact superpose b5e72644 b5e203
            | exact resolve b5e203 b5e72644
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e203 b5e72644
          have b5e72685 : (σ x) = (σ (k x x)) ∨ y = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e72672
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e72672
            | exact resolve b5e72672 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72672
          have b5e72722 : (k x x) = (τ (σ x)) ∨ y = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e14 (k x x)
               have i₂ := b5e72685
               grind)
            | exact superpose b5e72685 b5e14
            | exact resolve b5e14 b5e72685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72685
          have b5e72776 : y = (k y y) ∨ x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e72722
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e72722
            | exact resolve b5e72722 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72722
          have b5e72808 : x = y ∨ x = y ∨ x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e72350
               have i₂ := b5e72776
               grind)
            | exact superpose b5e72776 b5e72350
            | exact resolve b5e72350 b5e72776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72350 b5e72776
          have b5e72901 : x = (k x x) ∨ x = y := by grind
          clear b5e72808
          have b5e73061 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e9705 x x
               have i₂ := b5e72901
               grind)
            | exact superpose b5e72901 b5e9705
            | (have j0 := b5e9705 x x
               grind)
            | exact resolve b5e9705 b5e72901
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9705 b5e72901
          have b5e73066 : x = (M.op x x) ∨ x = y := by grind
          clear b5e73061
          have b5e73111 : (σ x) ≠ (σ x) ∨ x = y := by
            first
            | (have i₁ := b5e219
               have i₂ := b5e73066
               grind)
            | exact superpose b5e73066 b5e219
            | exact resolve b5e219 b5e73066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e219 b5e73066
          have b5e73168 : x = y := by grind
          clear b5e73111
          have b5e73212 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e73168
               grind)
            | exact superpose b5e73168 b5e24
            | exact resolve b5e24 b5e73168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73224 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e221
               have i₂ := b5e73168
               grind)
            | exact superpose b5e73168 b5e221
            | exact resolve b5e221 b5e73168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e221 b5e73168
          have b5e73243 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e73224
          have b5e73248 : False := by grind
          exact b5e73248
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
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
        have b6e26 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e25
             grind)
          | exact superpose b6e25 b6e13
          | exact resolve b6e13 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : x = (k x y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e28 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
        have b6e39 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e28 (σ x)
             grind)
          | exact superpose b6e28 b6e19
          | exact resolve b6e19 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e40 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e39
          | exact resolve b6e39 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b6e60 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e27
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e27 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e71 : x = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e20
             grind)
          | exact resolve b6e60 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e76 : x = (M.op x y) := by
          first
          | (have r₁ := b6e71
             have r₂ := b6e21
             grind)
          | exact resolve b6e71 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e78 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e76
             grind)
          | exact superpose b6e76 b6e40
          | exact resolve b6e40 b6e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e76
        have b6e418 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e58 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e58
          | exact resolve b6e58 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e485 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b6e418
        have b6e504 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e485
             have r₂ := b6e78
             grind)
          | exact resolve b6e485 b6e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e485
        have b6e541 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e504
             grind)
          | exact superpose b6e504 b6e13
          | exact resolve b6e13 b6e504
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e563 : y = (k x x) := by
          first
          | (have i₁ := b6e541
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e541
          | exact resolve b6e541 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e541
        have b6e635 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e563
             grind)
          | exact superpose b6e563 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e563
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e563
        have b6e636 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e635
        have b6e638 : x = (M.op x x) := by
          first
          | (have r₁ := b6e636
             have r₂ := b6e20
             grind)
          | exact resolve b6e636 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e636
        have b6e675 : x = (k x x) := by grind
        clear b6e638
        have b6e793 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e504
             have i₂ := b6e675
             grind)
          | exact superpose b6e675 b6e504
          | exact resolve b6e504 b6e675
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e504 b6e675
        have b6e804 : False := by grind
        exact b6e804
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) := by grind
          have b7e31 : (σ y) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e29
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e32 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e31
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e31
            | exact resolve b7e31 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e37 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e32
               grind)
            | exact superpose b7e32 b7e14
            | exact resolve b7e14 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e38 : y = (k y x) := by
            first
            | (have i₁ := b7e37
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e37
            | exact resolve b7e37 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e45 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e48 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e50 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e51 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e26 (σ y)
               grind)
            | exact superpose b7e26 b7e50
            | exact resolve b7e50 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e52 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e51
            | exact resolve b7e51 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e55 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e52
               grind)
            | exact superpose b7e52 b7e14
            | exact resolve b7e14 b7e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e56 : x = (k x y) := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e55
            | exact resolve b7e55 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b7e83 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e84 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e83
               have r₂ := b7e21
               grind)
            | exact resolve b7e83 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e86 : x = (M.op x y) := by
            first
            | (have r₁ := b7e84
               have r₂ := b7e22
               grind)
            | exact resolve b7e84 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e95 : x ≠ y ∨ x = (M.op y y) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b7e17 y x
               have i₂ := b7e86
               grind)
            | exact superpose b7e86 b7e17
            | (have j0 := b7e17 y x
               grind)
            | exact resolve b7e17 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e96 : y = (M.op x x) ∨ x ≠ y ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e95
               have i₂ := b7e38
               grind)
            | exact superpose b7e38 b7e95
            | exact resolve b7e95 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e95
          have b7e97 : x ≠ y ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e96
               have r₂ := b7e21
               grind)
            | exact resolve b7e96 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e458 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e26 (σ X0)
               have i₂ := b7e64 y X0
               grind)
            | exact superpose b7e64 b7e26
            | (have j1 := b7e64 y X0
               grind)
            | exact resolve b7e26 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e484 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e458 X0
               have i₂ := b7e26 (σ y)
               grind)
            | exact superpose b7e26 b7e458
            | (have j0 := b7e458 X0
               grind)
            | exact resolve b7e458 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e458
          have b7e523 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b7e484 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e484
            | (have j0 := b7e484 X0
               grind)
            | exact resolve b7e484 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e484
          have b7e3500 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e26 (σ y)
               have i₂ := b7e523 y
               grind)
            | exact superpose b7e523 b7e26
            | (have j1 := b7e523 y
               grind)
            | exact resolve b7e26 b7e523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e523
          have b7e3563 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3500
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e3500
            | exact resolve b7e3500 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3500
          have b7e3599 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3563
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e3563
            | exact resolve b7e3563 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3563
          have b7e3600 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e3599
          have b7e3630 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e3600
               grind)
            | exact superpose b7e3600 b7e14
            | exact resolve b7e14 b7e3600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3673 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3630
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e3630
            | exact resolve b7e3630 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3630
          have b7e3841 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e3673
               grind)
            | exact superpose b7e3673 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e3673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3673
          have b7e3842 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3841
          have b7e4848 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3842
          have b7e5113 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3600
               have i₂ := b7e4848
               grind)
            | exact superpose b7e4848 b7e3600
            | exact resolve b7e3600 b7e4848
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3600 b7e4848
          have b7e5132 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e5113
          have b7e5240 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y y
               have i₂ := b7e5132
               grind)
            | exact superpose b7e5132 b7e13
            | exact resolve b7e13 b7e5132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6243 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e5132
               have i₂ := b7e5240 y
               grind)
            | exact superpose b7e5240 b7e5132
            | exact resolve b7e5132 b7e5240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5132 b7e5240
          have b7e6286 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
          clear b7e6243
          have b7e6291 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e6286
               have r₂ := b7e22
               grind)
            | exact resolve b7e6286 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6286
          have b7e6739 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e6291
               grind)
            | exact superpose b7e6291 b7e14
            | exact resolve b7e14 b7e6291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6291
          have b7e6797 : x = y := by
            first
            | (have i₁ := b7e6739
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e6739
            | exact resolve b7e6739 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6739
          have b7e7041 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e6797
               grind)
            | exact superpose b7e6797 b7e22
            | exact resolve b7e22 b7e6797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7053 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e97
               have i₂ := b7e6797
               grind)
            | exact superpose b7e6797 b7e97
            | (have r₁ := b7e97
               have r₂ := b7e6797
               grind)
            | exact resolve b7e97 b7e6797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e6797
          have b7e7061 : x = (M.op x x) := by grind
          clear b7e7053
          have b7e7065 : False := by grind
          exact b7e7065
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b8e184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e185 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e184
               have r₂ := b8e24
               grind)
            | exact resolve b8e184 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e186 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e185
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e185
            | exact resolve b8e185 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185
          have b8e189 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e186
               grind)
            | exact superpose b8e186 b8e20
            | exact resolve b8e20 b8e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e189
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e189
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e189 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e189
          have b8e211 : y = (M.op x x) ∨ x = (M.op y x) := by grind
          clear b8e210
          have b8e214 : x = (M.op y x) := by
            first
            | (have r₁ := b8e211
               have r₂ := b8e21
               grind)
            | exact resolve b8e211 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211
          have b8e217 : False := by grind
          exact b8e217

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_x_pxy_Equation327 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law327 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
      have b0e26 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
      have b0e42 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e26 (σ x)
           grind)
        | exact superpose b0e26 b0e18
        | exact resolve b0e18 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e43 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e42
        | exact resolve b0e42 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e45 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e25 x
           grind)
        | exact superpose b0e25 b0e43
        | exact resolve b0e43 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e43
      have b0e46 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e45
        | exact resolve b0e45 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e47 : False := by grind
      exact b0e47
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b1e101 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e32 X1 X0
             grind)
          | exact superpose b1e32 b1e13
          | exact resolve b1e13 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e238 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e101
        have b1e253 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e238 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e238
          | exact resolve b1e238 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e238
        have b1e453 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e64 x x
             grind)
          | exact superpose b1e64 b1e21
          | (have j1 := b1e64 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e64 x y
             grind)
          | exact resolve b1e21 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e508 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e453
        have b1e1045 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e508
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e508
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e508 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e508
        have b1e1046 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1045
        have b1e1047 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1046
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1046
          | exact resolve b1e1046 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1046
        have b1e1048 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1047
        have b1e1054 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1048
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1048
          | exact resolve b1e1048 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1048
        have b1e1067 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e253 x
             have i₂ := b1e1054
             grind)
          | exact superpose b1e1054 b1e253
          | exact resolve b1e253 b1e1054
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e253 b1e1054
        have b1e1079 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e1067
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1067
          | exact resolve b1e1067 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1067
        have b1e1181 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e1079
             grind)
          | exact superpose b1e1079 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e1079
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1079
        have b1e1182 : x = (M.op x x) ∨ x = y := by grind
        clear b1e1181
        have b1e1191 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1182
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1182
          | exact resolve b1e1182 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1182
        have b1e1192 : x = y := by grind
        clear b1e1191
        have b1e1229 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1192
             grind)
          | exact superpose b1e1192 b1e22
          | exact resolve b1e22 b1e1192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1456 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1229
             grind)
          | exact superpose b1e1229 b1e21
          | exact resolve b1e21 b1e1229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1229
        have b1e1474 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e1456
             have i₂ := b1e1192
             grind)
          | exact superpose b1e1192 b1e1456
          | exact resolve b1e1456 b1e1192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1192 b1e1456
        have b1e1475 : False := by grind
        exact b1e1475
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
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
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e31 X1 X0
             grind)
          | exact superpose b2e31 b2e13
          | exact resolve b2e13 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b2e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
        have b2e116 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e48
        have b2e130 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e116 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e116
          | exact resolve b2e116 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116
        have b2e214 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e65 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e215 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e214
             have r₂ := b2e22
             grind)
          | exact resolve b2e214 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e214
        have b2e216 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e215
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e215
          | exact resolve b2e215 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e215
        have b2e217 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e216
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e216
          | exact resolve b2e216 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e216
        have b2e220 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e217
             grind)
          | exact superpose b2e217 b2e19
          | exact resolve b2e19 b2e217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e217
        have b2e226 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e220
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e220
          | exact resolve b2e220 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e220
        have b2e227 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e226
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e226
          | exact resolve b2e226 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e226
        have b2e354 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e57 x x
             grind)
          | exact superpose b2e57 b2e21
          | (have j1 := b2e57 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e57 x y
             grind)
          | exact resolve b2e21 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e408 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e354
        have b2e935 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e408
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e408
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e408 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e408
        have b2e936 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e935
        have b2e937 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e936
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e936
          | exact resolve b2e936 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e936
        have b2e938 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e937
        have b2e944 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e938
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e938
          | exact resolve b2e938 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e938
        have b2e957 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e130 x
             have i₂ := b2e944
             grind)
          | exact superpose b2e944 b2e130
          | exact resolve b2e130 b2e944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130 b2e944
        have b2e969 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e957
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e957
          | exact resolve b2e957 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e957
        have b2e1007 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e969
             grind)
          | exact superpose b2e969 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e969
        have b2e1008 : x = (M.op x x) ∨ x = y := by grind
        clear b2e1007
        have b2e1017 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e1008
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1008
          | exact resolve b2e1008 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1008
        have b2e1018 : x = y := by grind
        clear b2e1017
        have b2e1057 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e227
             have i₂ := b2e1018
             grind)
          | exact superpose b2e1018 b2e227
          | exact resolve b2e227 b2e1018
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e227 b2e1018
        have b2e1059 : False := by grind
        exact b2e1059
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
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
        have b3e29 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
        have b3e49 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e29 (σ x)
             grind)
          | exact superpose b3e29 b3e19
          | exact resolve b3e19 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e54 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e49
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e49
          | exact resolve b3e49 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e55 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e28 x
             grind)
          | exact superpose b3e28 b3e54
          | exact resolve b3e54 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e54
        have b3e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b3e450 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e63 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e63
          | exact resolve b3e63 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e518 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e450
        have b3e682 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e518
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e518
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e518 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e694 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e682
        have b3e706 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e694
             have r₂ := b3e55
             grind)
          | exact resolve b3e694 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e694
        have b3e781 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e706
        have b3e891 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e518
             have i₂ := b3e781
             grind)
          | exact superpose b3e781 b3e518
          | exact resolve b3e518 b3e781
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e518 b3e781
        have b3e898 : (σ x) = (σ y) := by grind
        clear b3e891
        have b3e968 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e898
             grind)
          | exact superpose b3e898 b3e13
          | exact resolve b3e13 b3e898
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e999 : x = y := by
          first
          | (have i₁ := b3e968
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e968
          | exact resolve b3e968 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e968
        have b3e1085 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e999
             grind)
          | exact superpose b3e999 b3e19
          | exact resolve b3e19 b3e999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1086 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e999
             grind)
          | exact superpose b3e999 b3e21
          | exact resolve b3e21 b3e999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e999
        have b3e1093 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1085
             have i₂ := b3e1086
             grind)
          | exact superpose b3e1086 b3e1085
          | exact resolve b3e1085 b3e1086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1085 b3e1086
        have b3e1094 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1093
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1093
          | exact resolve b3e1093 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1093
        have b3e1095 : False := by grind
        exact b3e1095
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e35 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e27 (σ x)
               grind)
            | exact superpose b4e27 b4e20
            | exact resolve b4e20 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e39 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e35
               have i₂ := b4e26 x
               grind)
            | exact superpose b4e26 b4e35
            | exact resolve b4e35 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e35
          have b4e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b4e94 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e34 X1 X0
               grind)
            | exact superpose b4e34 b4e14
            | exact resolve b4e14 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e225 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b4e94
          have b4e240 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e225 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e225
            | exact resolve b4e225 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e225
          have b4e418 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e62 x x
               grind)
            | exact superpose b4e62 b4e39
            | (have j1 := b4e62 x x
               grind)
            | (have r₁ := b4e39
               have r₂ := b4e62 x (M.op x x)
               grind)
            | exact resolve b4e39 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e468 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e62 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e469 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e468 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e468
          have b4e476 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e418
          have b4e951 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e469 (τ X0)
               have i₂ := b4e34 X0 (τ X0)
               grind)
            | exact superpose b4e34 b4e469
            | (have j0 := b4e469 (τ X0)
               grind)
            | exact resolve b4e469 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e955 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e951 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e951
            | (have j0 := b4e951 X0
               grind)
            | exact resolve b4e951 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e951
          have b4e959 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e955 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e955
            | (have j0 := b4e955 X0
               grind)
            | exact resolve b4e955 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e955
          have b4e2839 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e476
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e476
            | (have j1 := b4e18 (σ x) (σ x)
               grind)
            | exact resolve b4e476 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e476
          have b4e2840 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e2839
          have b4e2841 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e2840
          have b4e2868 : x = (k x (τ (σ x))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e240 x
               have i₂ := b4e2841
               grind)
            | exact superpose b4e2841 b4e240
            | exact resolve b4e240 b4e2841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e240 b4e2841
          have b4e2885 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e2868
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e2868
            | exact resolve b4e2868 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2868
          have b4e2886 : x = (M.op x x) := by
            first
            | (have j1 := b4e959 x
               grind)
            | (have r₁ := b4e2885
               have r₂ := b4e959 x
               grind)
            | exact resolve b4e2885 b4e959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e959 b4e2885
          have b4e2933 : x = (k x x) := by grind
          have b4e3103 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e469 x
               have i₂ := b4e2933
               grind)
            | exact superpose b4e2933 b4e469
            | (have j0 := b4e469 x
               grind)
            | exact resolve b4e469 b4e2933
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e469 b4e2933
          have b4e3120 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e3103
          have b4e3567 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e3120
               grind)
            | exact superpose b4e3120 b4e39
            | exact resolve b4e39 b4e3120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e3120
          have b4e3590 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e3567
               have i₂ := b4e2886
               grind)
            | exact superpose b4e2886 b4e3567
            | exact resolve b4e3567 b4e2886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2886 b4e3567
          have b4e3591 : False := by grind
          exact b4e3591
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e40 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          clear b5e40
          have b5e46 : x = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b5e59 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b5e74 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e33 X1 X0
               grind)
            | exact superpose b5e33 b5e14
            | exact resolve b5e14 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e159 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 X0 X2
               have i₂ := b5e59 X0 X0 X1
               grind)
            | (have i₁ := b5e18 X2 X1
               have i₂ := b5e59 X0 X2 X2
               grind)
            | exact superpose b5e59 b5e18
            | (have j0 := b5e18 X1 X0
               have j1 := b5e59 X0 X1 X1
               grind)
            | exact resolve b5e18 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e205 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e206 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e205
               have r₂ := b5e24
               grind)
            | exact resolve b5e205 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e205
          have b5e207 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e206
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e206
            | exact resolve b5e206 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e206
          have b5e208 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e207
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e207
            | exact resolve b5e207 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e207
          have b5e211 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e208
               grind)
            | exact superpose b5e208 b5e20
            | exact resolve b5e20 b5e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e217 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e211
               have i₂ := b5e26 x
               grind)
            | exact superpose b5e26 b5e211
            | exact resolve b5e211 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e211
          have b5e377 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e53 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e53 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e53 X0 X1
               grind)
            | exact resolve b5e17 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e389 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e377 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e377
          have b5e390 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e389 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e389
          have b5e400 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e390 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e390
            | (have j0 := b5e390 X0 X1
               grind)
            | exact resolve b5e390 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e390
          have b5e6012 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b5e400
          have b5e6052 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e6012 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e6012
            | (have j0 := b5e6012 X0 X1
               grind)
            | exact resolve b5e6012 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6012
          have b5e6053 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e6052 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6052
          have b5e7513 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e6053 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e6053
            | exact resolve b5e6053 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7637 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7513 X0 X1
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e7513
            | (have j0 := b5e7513 X0 X1
               grind)
            | exact resolve b5e7513 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7513
          have b5e7643 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7637 X0 X1
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e7637
            | (have j0 := b5e7637 X0 X1
               grind)
            | exact resolve b5e7637 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e7637
          have b5e7905 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e7643 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e7643
            | exact resolve b5e7643 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7643
          have b5e8512 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e7905 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7905
          have b5e9263 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e8512 X0 (M.op X1 X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e8512
            | (have j0 := b5e8512 X0 X1
               grind)
            | exact resolve b5e8512 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8512
          have b5e10299 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e159 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e159
          have b5e10301 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e10299 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10299
          have b5e10302 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e10301 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10301
          have b5e12131 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e9263 (σ x) (σ y) X0
               have i₂ := b5e208
               grind)
            | exact superpose b5e208 b5e9263
            | (have j0 := b5e9263 (σ x) (σ y) X0
               grind)
            | (have r₁ := b5e9263 (σ x) (σ y) x
               have r₂ := b5e208
               grind)
            | exact resolve b5e9263 b5e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9263
          have b5e12151 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have j0 := b5e12131 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12131
          have b5e13366 : ∀ X0 : G, (k x (τ (M.op (σ y) X0))) = (τ (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e74 x (M.op (σ y) X0)
               have i₂ := b5e12151 X0
               grind)
            | exact superpose b5e12151 b5e74
            | exact resolve b5e74 b5e12151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74 b5e12151
          have b5e13396 : ∀ X0 : G, x = (k x (τ (M.op (σ y) X0))) := by
            intro X0
            first
            | (have i₁ := b5e13366 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e13366
            | exact resolve b5e13366 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13366
          have b5e14230 : ∀ X0 : G, x = (k x (τ (σ (k y X0)))) ∨ (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b5e13396 (σ X0)
               have i₂ := b5e6053 X0 y
               grind)
            | exact superpose b5e6053 b5e13396
            | (have j1 := b5e6053 X0 y
               grind)
            | exact resolve b5e13396 b5e6053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6053 b5e13396
          have b5e14284 : ∀ X0 : G, x = (k x (k y X0)) ∨ (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b5e14230 X0
               have i₂ := b5e14 (k y X0)
               grind)
            | exact superpose b5e14 b5e14230
            | (have j0 := b5e14230 X0
               grind)
            | exact resolve b5e14230 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14230
          have b5e19438 : x = (k x (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e14284 y
               have i₂ := b5e10302 y
               grind)
            | exact superpose b5e10302 b5e14284
            | (have j1 := b5e10302 y
               grind)
            | exact resolve b5e14284 b5e10302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10302 b5e14284
          have b5e19513 : x = (k x (M.op y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e19438
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e19438
            | exact resolve b5e19438 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19438
          have b5e19531 : x = (k x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e19513
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e19513
            | exact resolve b5e19513 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19513
          have b5e19534 : (σ y) = (σ (M.op y x)) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e19531
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e19531
            | exact resolve b5e19531 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19531
          have b5e19535 : (σ x) = (σ y) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e19534
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e19534
            | exact resolve b5e19534 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19534
          have b5e19536 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e19535
               have i₂ := b5e26 y
               grind)
            | exact superpose b5e26 b5e19535
            | exact resolve b5e19535 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e19535
          have b5e19537 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e19536
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e19536
            | exact resolve b5e19536 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19536
          have b5e19848 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e19537
               grind)
            | exact superpose b5e19537 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e19537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19537
          have b5e19879 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
          clear b5e19848
          have b5e20995 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e217
               have i₂ := b5e19879
               grind)
            | exact superpose b5e19879 b5e217
            | exact resolve b5e217 b5e19879
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e217 b5e19879
          have b5e21040 : (σ x) = (σ y) ∨ x = y := by grind
          clear b5e20995
          have b5e21201 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e21040
               grind)
            | exact superpose b5e21040 b5e14
            | exact resolve b5e14 b5e21040
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21040
          have b5e21298 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e21201
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e21201
            | exact resolve b5e21201 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21201
          have b5e21299 : x = y := by grind
          clear b5e21298
          have b5e21464 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e21299
               grind)
            | exact superpose b5e21299 b5e24
            | exact resolve b5e24 b5e21299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e21473 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e208
               have i₂ := b5e21299
               grind)
            | exact superpose b5e21299 b5e208
            | exact resolve b5e208 b5e21299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e208 b5e21299
          have b5e21491 : False := by grind
          exact b5e21491
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
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
        have b6e26 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e25
             grind)
          | exact superpose b6e25 b6e13
          | exact resolve b6e13 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : x = (k x y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e28 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
        have b6e39 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e28 (σ x)
             grind)
          | exact superpose b6e28 b6e19
          | exact resolve b6e19 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e40 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e39
          | exact resolve b6e39 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b6e60 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e27
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e27 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e71 : x = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e20
             grind)
          | exact resolve b6e60 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e76 : x = (M.op x y) := by
          first
          | (have r₁ := b6e71
             have r₂ := b6e21
             grind)
          | exact resolve b6e71 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e78 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e76
             grind)
          | exact superpose b6e76 b6e40
          | exact resolve b6e40 b6e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e76
        have b6e416 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e58 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e58
          | exact resolve b6e58 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e483 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b6e416
        have b6e502 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e483
             have r₂ := b6e78
             grind)
          | exact resolve b6e483 b6e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e483
        have b6e539 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e502
             grind)
          | exact superpose b6e502 b6e13
          | exact resolve b6e13 b6e502
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e561 : y = (k x x) := by
          first
          | (have i₁ := b6e539
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e539
          | exact resolve b6e539 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e539
        have b6e633 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e561
             grind)
          | exact superpose b6e561 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e561
        have b6e634 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e633
        have b6e636 : x = (M.op x x) := by
          first
          | (have r₁ := b6e634
             have r₂ := b6e20
             grind)
          | exact resolve b6e634 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e634
        have b6e673 : x = (k x x) := by grind
        clear b6e636
        have b6e791 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e502
             have i₂ := b6e673
             grind)
          | exact superpose b6e673 b6e502
          | exact resolve b6e502 b6e673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e502 b6e673
        have b6e802 : False := by grind
        exact b6e802
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e45 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e48 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e50 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e53 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e14
            | exact resolve b7e14 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : x = (k x y) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e53
            | exact resolve b7e53 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b7e81 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e82 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e81
               have r₂ := b7e21
               grind)
            | exact resolve b7e81 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e84 : x = (M.op x y) := by
            first
            | (have r₁ := b7e82
               have r₂ := b7e22
               grind)
            | exact resolve b7e82 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e489 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e26 (σ X0)
               have i₂ := b7e62 y X0
               grind)
            | exact superpose b7e62 b7e26
            | (have j1 := b7e62 y X0
               grind)
            | exact resolve b7e26 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e516 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e489 X0
               have i₂ := b7e26 (σ y)
               grind)
            | exact superpose b7e26 b7e489
            | (have j0 := b7e489 X0
               grind)
            | exact resolve b7e489 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e489
          have b7e558 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b7e516 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e516
            | (have j0 := b7e516 X0
               grind)
            | exact resolve b7e516 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e516
          have b7e3384 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e26 (σ y)
               have i₂ := b7e558 y
               grind)
            | exact superpose b7e558 b7e26
            | (have j1 := b7e558 y
               grind)
            | exact resolve b7e26 b7e558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e558
          have b7e3446 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3384
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e3384
            | exact resolve b7e3384 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3384
          have b7e3478 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3446
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e3446
            | exact resolve b7e3446 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3446
          have b7e3479 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e3478
          have b7e3499 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e3479
               grind)
            | exact superpose b7e3479 b7e14
            | exact resolve b7e14 b7e3479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3542 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3499
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e3499
            | exact resolve b7e3499 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3499
          have b7e3712 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e3542
               grind)
            | exact superpose b7e3542 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e3542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3542
          have b7e3713 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3712
          have b7e4402 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3713
          have b7e4929 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3479
               have i₂ := b7e4402
               grind)
            | exact superpose b7e4402 b7e3479
            | exact resolve b7e3479 b7e4402
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3479 b7e4402
          have b7e4948 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e4929
          have b7e5056 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y y
               have i₂ := b7e4948
               grind)
            | exact superpose b7e4948 b7e13
            | exact resolve b7e13 b7e4948
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6129 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e4948
               have i₂ := b7e5056 y
               grind)
            | exact superpose b7e5056 b7e4948
            | exact resolve b7e4948 b7e5056
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4948 b7e5056
          have b7e6172 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
          clear b7e6129
          have b7e6177 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e6172
               have r₂ := b7e22
               grind)
            | exact resolve b7e6172 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6172
          have b7e6788 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e6177
               grind)
            | exact superpose b7e6177 b7e14
            | exact resolve b7e14 b7e6177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6177
          have b7e6846 : x = y := by
            first
            | (have i₁ := b7e6788
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e6788
            | exact resolve b7e6788 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6788
          have b7e7330 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e6846
               grind)
            | exact superpose b7e6846 b7e22
            | exact resolve b7e22 b7e6846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7340 : x = (M.op x x) := by
            first
            | (have i₁ := b7e84
               have i₂ := b7e6846
               grind)
            | exact superpose b7e6846 b7e84
            | exact resolve b7e84 b7e6846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84 b7e6846
          have b7e7349 : False := by grind
          exact b7e7349
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b8e184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e185 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e184
               have r₂ := b8e24
               grind)
            | exact resolve b8e184 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e186 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e185
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e185
            | exact resolve b8e185 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185
          have b8e189 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e186
               grind)
            | exact superpose b8e186 b8e20
            | exact resolve b8e20 b8e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e189
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e189
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e189 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e189
          have b8e211 : y = (M.op x x) ∨ x = (M.op y x) := by grind
          clear b8e210
          have b8e214 : x = (M.op y x) := by
            first
            | (have r₁ := b8e211
               have r₂ := b8e21
               grind)
            | exact resolve b8e211 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211
          have b8e217 : False := by grind
          exact b8e217

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_x_x_pxy_Equation327 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law327 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = a :=
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
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
        have b1e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
        have b1e26 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
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
        have b1e32 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e15 X0 x
             have i₂ := b1e25 X0
             grind)
          | exact superpose b1e25 b1e15
          | (have j0 := b1e15 X0 x
             grind)
          | exact resolve b1e15 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b1e42 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
        have b1e43 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have j1 := b1e15 (M.op (σ x) (σ y)) (σ x)
             grind)
          | (have r₁ := b1e42
             have r₂ := b1e15 (M.op (σ x) (σ y)) (σ x)
             grind)
          | exact resolve b1e42 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e83 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k (τ X0) X1)
             have i₂ := b1e35 X0 X1
             grind)
          | exact superpose b1e35 b1e13
          | exact resolve b1e13 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e94 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b1e32 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e32
          | (have j0 := b1e32 x
             grind)
          | exact resolve b1e32 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e386 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e56 X0 x
             have i₂ := b1e26 (σ X0)
             grind)
          | exact superpose b1e26 b1e56
          | (have j0 := b1e56 X0 x
             grind)
          | exact resolve b1e56 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e474 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e386 X0
             have i₂ := b1e26 (σ x)
             grind)
          | exact superpose b1e26 b1e386
          | (have j0 := b1e386 X0
             grind)
          | exact resolve b1e386 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e386
        have b1e728 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) := by
          first
          | (have i₁ := b1e83 (M.op (σ x) (σ y)) x
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e83
          | exact resolve b1e83 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e83
        have b1e7676 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e474 x
             grind)
          | exact superpose b1e474 b1e21
          | (have j1 := b1e474 x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e474 y
             grind)
          | exact resolve b1e21 b1e474
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e474
        have b1e7827 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b1e7676
        have b1e8071 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e7827
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e7827
          | (have j1 := b1e17 x x
             grind)
          | exact resolve b1e7827 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7827
        have b1e8073 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
        clear b1e8071
        have b1e8075 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e8073
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e8073
          | exact resolve b1e8073 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8073
        have b1e8081 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e8075
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8075
          | exact resolve b1e8075 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8075
        have b1e8082 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
        clear b1e8081
        have b1e8089 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e8082
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e8082
          | exact resolve b1e8082 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8082
        have b1e8092 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e8089
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8089
          | exact resolve b1e8089 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8089
        have b1e8220 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = y := by
          first
          | (have i₁ := b1e728
             have i₂ := b1e8092
             grind)
          | exact superpose b1e8092 b1e728
          | exact resolve b1e728 b1e8092
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e728 b1e8092
        have b1e8286 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e8220
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e8220
          | exact resolve b1e8220 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8220
        have b1e8294 : x = (k x x) := by
          first
          | (have r₁ := b1e8286
             have r₂ := b1e94
             grind)
          | exact resolve b1e8286 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e94 b1e8286
        have b1e8814 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e8294
             grind)
          | exact superpose b1e8294 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e8294
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8294
        have b1e8822 : x = (M.op x x) := by grind
        clear b1e8814
        have b1e8836 : x = (M.op x y) := by
          first
          | (have i₁ := b1e8822
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e8822
          | exact resolve b1e8822 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e8822
        have b1e8846 : x = y := by
          first
          | (have i₁ := b1e8836
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8836
          | exact resolve b1e8836 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8836
        have b1e9369 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e8846
             grind)
          | exact superpose b1e8846 b1e21
          | exact resolve b1e21 b1e8846
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e9414 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e9369
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e9369
          | exact resolve b1e9369 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9369
        have b1e9417 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e9414
             have i₂ := b1e8846
             grind)
          | exact superpose b1e8846 b1e9414
          | exact resolve b1e9414 b1e8846
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8846 b1e9414
        have b1e9418 : False := by grind
        exact b1e9418
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
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
        have b2e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
        have b2e28 : y ≠ y ∨ x = (k x y) := by
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
        have b2e29 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X1 X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 X0)
             have r₂ := b2e12 X0 X0 X0
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e15 X0 x
             have i₂ := b2e25 X0
             grind)
          | exact superpose b2e25 b2e15
          | (have j0 := b2e15 X0 x
             grind)
          | exact resolve b2e15 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : x = (k x y) := by grind
        clear b2e28
        have b2e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e39 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by grind
        have b2e40 : (M.op x y) = (k (M.op x y) x) := by
          first
          | (have j1 := b2e15 (M.op x y) x
             grind)
          | (have r₁ := b2e39
             have r₂ := b2e15 (M.op x y) x
             grind)
          | exact resolve b2e39 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39
        have b2e42 : y = (k y x) := by
          first
          | (have i₁ := b2e40
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e40
          | exact resolve b2e40 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e52 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
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
        have b2e53 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e57 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e57 X0 X1
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e57 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e74 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e33 X1 X0
             grind)
          | exact superpose b2e33 b2e13
          | exact resolve b2e13 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e59 (σ X0) (σ X1)
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e59
          | exact resolve b2e59 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e78 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e33 X1 X0
             have i₂ := b2e59 X0 (τ X1)
             grind)
          | exact superpose b2e59 b2e33
          | (have j1 := b2e59 X0 (τ X1)
             grind)
          | exact resolve b2e33 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e86 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b2e30 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e30
          | (have j0 := b2e30 x
             grind)
          | exact resolve b2e30 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e95 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e29 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e181 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e52 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e182 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e181
             have r₂ := b2e21
             grind)
          | exact resolve b2e181 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e181
        have b2e183 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e182
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e182
          | exact resolve b2e182 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182
        have b2e184 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e183
             have i₂ := b2e31
             grind)
          | exact superpose b2e31 b2e183
          | exact resolve b2e183 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e183
        have b2e187 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e184
             grind)
          | exact superpose b2e184 b2e21
          | exact resolve b2e21 b2e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e297 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b2e327 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e48 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e329 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e327 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e327
        have b2e331 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e297 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e297
        have b2e344 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e331 X0
             have j1 := b2e15 (σ (k X0 X0)) (σ X0)
             grind)
          | (have r₁ := b2e331 X0
             have r₂ := b2e15 (σ (k X0 X0)) (σ X0)
             grind)
          | (have r₁ := b2e331 X0
             have r₂ := b2e15 (σ X0) (σ X0)
             grind)
          | exact resolve b2e331 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e331
        have b2e358 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e344 X0
             have i₂ := b2e18 (k X0 X0) X0
             grind)
          | exact superpose b2e18 b2e344
          | (have j0 := b2e344 X0
             grind)
          | exact resolve b2e344 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e344
        have b2e374 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e74 X0 (M.op (σ X0) (σ X0))
             have i₂ := b2e95 (σ X0)
             grind)
          | exact superpose b2e95 b2e74
          | exact resolve b2e74 b2e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e383 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e374 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e374
          | exact resolve b2e374 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e374
        have b2e855 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e329 (τ X0)
             have i₂ := b2e33 X0 (τ X0)
             grind)
          | exact superpose b2e33 b2e329
          | (have j0 := b2e329 (τ X0)
             grind)
          | exact resolve b2e329 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e329
        have b2e859 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e855 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e855
          | (have j0 := b2e855 X0
             grind)
          | exact resolve b2e855 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e855
        have b2e862 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e859 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e859
          | (have j0 := b2e859 X0
             grind)
          | exact resolve b2e859 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e859
        have b2e901 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e78 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e78
          | exact resolve b2e78 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e78
        have b2e937 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e901 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e901
          | (have j0 := b2e901 X0 X1
             grind)
          | exact resolve b2e901 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e901
        have b2e1006 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (σ X0) (σ X1)
             have i₂ := b2e77 X0 X1
             grind)
          | exact superpose b2e77 b2e12
          | (have j1 := b2e77 X0 X1
             grind)
          | exact resolve b2e12 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e1613 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e33 X0 (k (τ X0) (τ X0))
             have i₂ := b2e358 (τ X0)
             grind)
          | exact superpose b2e358 b2e33
          | (have j1 := b2e358 (τ X0)
             grind)
          | exact resolve b2e33 b2e358
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e358
        have b2e1650 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e1613 X0
             have i₂ := b2e33 X0 (τ X0)
             grind)
          | exact superpose b2e33 b2e1613
          | (have j0 := b2e1613 X0
             grind)
          | exact resolve b2e1613 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e1613
        have b2e1656 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e1650 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1650
          | (have j0 := b2e1650 X0
             grind)
          | exact resolve b2e1650 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1650
        have b2e1661 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1656 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1656
          | (have j0 := b2e1656 X0
             grind)
          | exact resolve b2e1656 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1656
        have b2e1698 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e74 (k X0 X1) X2
             have i₂ := b2e937 X1 X0
             grind)
          | exact superpose b2e937 b2e74
          | (have j1 := b2e937 X1 X0
             grind)
          | exact resolve b2e74 b2e937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e937
        have b2e1703 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1698 X0 X1 X2
             have i₂ := b2e74 (M.op X0 X1) X2
             grind)
          | exact superpose b2e74 b2e1698
          | (have j0 := b2e1698 X0 X1 X2
             grind)
          | exact resolve b2e1698 b2e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74 b2e1698
        have b2e49495 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X0) = (k (k X1 X2) X0) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1703 X0 X1 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1703
          | (have j0 := b2e1703 X1 X2 X2
             grind)
          | exact resolve b2e1703 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1703
        have b2e49894 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1661 X0
             have i₂ := b2e49495 X0 X0 X0
             grind)
          | exact superpose b2e49495 b2e1661
          | (have j0 := b2e1661 X0
             have j1 := b2e49495 X0 X0 X0
             grind)
          | exact resolve b2e1661 b2e49495
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1661 b2e49495
        have b2e49997 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e49894 X0
             have j1 := b2e862 X0
             grind)
          | (have r₁ := b2e49894 X0
             have r₂ := b2e862 X0
             grind)
          | exact resolve b2e49894 b2e862
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e862 b2e49894
        have b2e50207 : (k (M.op x y) x) = (k x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e49997 x
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e49997
          | exact resolve b2e49997 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e49997
        have b2e50285 : (k y x) = (k x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e50207
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e50207
          | exact resolve b2e50207 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50207
        have b2e50297 : y = (k x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e50285
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e50285
          | exact resolve b2e50285 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e50285
        have b2e50300 : y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e50297
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e50297
          | exact resolve b2e50297 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50297
        have b2e50628 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e1006 x x x
             have i₂ := b2e50300
             grind)
          | exact superpose b2e50300 b2e1006
          | exact resolve b2e1006 b2e50300
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1006
        have b2e50674 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b2e50628 X0
             grind)
          | (have r₁ := b2e50628 X0
             have r₂ := b2e187
             grind)
          | exact resolve b2e50628 b2e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50628
        have b2e50983 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ x = y := by
          first
          | (have i₁ := b2e383 x
             have i₂ := b2e50674 (σ x)
             grind)
          | exact superpose b2e50674 b2e383
          | exact resolve b2e383 b2e50674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e383 b2e50674
        have b2e51011 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e50983
             have i₂ := b2e184
             grind)
          | exact superpose b2e184 b2e50983
          | exact resolve b2e50983 b2e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e184 b2e50983
        have b2e51025 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e51011
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e51011
          | exact resolve b2e51011 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51011
        have b2e51032 : x = (k x x) := by
          first
          | (have r₁ := b2e51025
             have r₂ := b2e86
             grind)
          | exact resolve b2e51025 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86 b2e51025
        have b2e51312 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e50300
             have i₂ := b2e51032
             grind)
          | exact superpose b2e51032 b2e50300
          | exact resolve b2e50300 b2e51032
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50300 b2e51032
        have b2e51382 : x = y := by grind
        clear b2e51312
        have b2e51679 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e187
             have i₂ := b2e51382
             grind)
          | exact superpose b2e51382 b2e187
          | exact resolve b2e187 b2e51382
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187 b2e51382
        have b2e51719 : False := by grind
        exact b2e51719
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
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
        have b3e26 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X0 (M.op X1 X2)
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b3e15 X0 (M.op X0 X0)
             have r₂ := b3e12 X0 X0 X0
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b3e47 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e44 X0 X1
             have j1 := b3e15 (M.op (M.op X0 X1) X0) (M.op X0 X1)
             grind)
          | (have r₁ := b3e44 X0 X1
             have r₂ := b3e15 (M.op (M.op X0 X1) X0) (M.op X0 X1)
             grind)
          | exact resolve b3e44 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e58 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X1 X2) X1 X2
             have i₂ := b3e17 X0 (M.op X1 X2)
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 (M.op X0 (M.op X1 X2)) X1
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 (M.op X1 X2)
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e60 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e58 X0 X1 X2
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e58
          | (have j0 := b3e58 X0 X1 X2
             grind)
          | exact resolve b3e58 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e63 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e60 X0 X1 X2
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e60
          | (have j0 := b3e60 X0 X1 X2
             grind)
          | exact resolve b3e60 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e323 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = X0 ∨ (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (M.op X0 X1) = (M.op X1 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e47 X1 X2
             have i₂ := b3e63 X0 X1 X2
             grind)
          | (have i₁ := b3e47 X0 X1
             have i₂ := b3e63 (M.op (M.op X0 X1) X0) X1 X2
             grind)
          | exact superpose b3e63 b3e47
          | (have j1 := b3e63 X0 X1 X2
             grind)
          | exact resolve b3e47 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e63
        have b3e338 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (k X0 (M.op X1 X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b3e323 X0 X1 X2
             have j1 := b3e30 X0 X1 X2
             grind)
          | (have r₁ := b3e323 X0 X1 X2
             have r₂ := b3e30 X0 X1 X2
             grind)
          | (have r₁ := b3e323 X1 X0 X1
             have r₂ := b3e30 X0 X1 X0
             grind)
          | exact resolve b3e323 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e323
        have b3e380 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e52 X0 x
             have i₂ := b3e26 (σ X0)
             grind)
          | exact superpose b3e26 b3e52
          | (have j0 := b3e52 X0 x
             grind)
          | exact resolve b3e52 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e466 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e380 X0
             have i₂ := b3e26 (σ x)
             grind)
          | exact superpose b3e26 b3e380
          | (have j0 := b3e380 X0
             grind)
          | exact resolve b3e380 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e380
        have b3e485 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e466 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e466
          | (have j0 := b3e466 X0
             grind)
          | exact resolve b3e466 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e466
        have b3e1260 : ∀ X0 : G, (M.op X0 y) = (k X0 x) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e338 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e338
          | exact resolve b3e338 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e338
        have b3e4711 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e485 x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e485
          | (have j0 := b3e485 (k x x)
             grind)
          | exact resolve b3e485 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e485
        have b3e4758 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e4711
        have b3e4794 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e4758
             grind)
          | exact superpose b3e4758 b3e13
          | exact resolve b3e13 b3e4758
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4758
        have b3e4840 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4794
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e4794
          | exact resolve b3e4794 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4794
        have b3e5034 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1260 x
             have i₂ := b3e4840
             grind)
          | exact superpose b3e4840 b3e1260
          | exact resolve b3e1260 b3e4840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1260 b3e4840
        have b3e5066 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b3e5034
             have r₂ := b3e20
             grind)
          | exact resolve b3e5034 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5034
        have b3e5128 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e5066
             grind)
          | exact superpose b3e5066 b3e13
          | exact resolve b3e13 b3e5066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5066
        have b3e5171 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e5128
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e5128
          | exact resolve b3e5128 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5128
        have b3e5172 : x = y := by grind
        clear b3e5171
        have b3e5457 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e5172
             grind)
          | exact superpose b3e5172 b3e24
          | exact resolve b3e24 b3e5172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e5490 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e5457
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e5457
          | exact resolve b3e5457 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5457
        have b3e5492 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e5490
             have i₂ := b3e5172
             grind)
          | exact superpose b3e5172 b3e5490
          | exact resolve b3e5490 b3e5172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5172 b3e5490
        have b3e5493 : False := by grind
        exact b3e5493
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
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
          have b4e27 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
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
          have b4e31 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X0 (M.op X1 X2)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 X0 (M.op X1 X2)
               grind)
            | (have r₁ := b4e16 X0 (M.op X0 X0)
               have r₂ := b4e13 X0 X0 X0
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b4e46 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e41 X0 X1
               have j1 := b4e16 (M.op (M.op X0 X1) X0) (M.op X0 X1)
               grind)
            | (have r₁ := b4e41 X0 X1
               have r₂ := b4e16 (M.op (M.op X0 X1) X0) (M.op X0 X1)
               grind)
            | exact resolve b4e41 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e58 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e61 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X1 X2) X1 X2
               have i₂ := b4e18 X0 (M.op X1 X2)
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 (M.op X0 (M.op X1 X2)) X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 (M.op X1 X2)
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58
          have b4e66 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e61 X0 X1 X2
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e61
            | (have j0 := b4e61 X0 X1 X2
               grind)
            | exact resolve b4e61 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61
          have b4e67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e64 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e64 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e64 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e71 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e66 X0 X1 X2
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e66
            | (have j0 := b4e66 X0 X1 X2
               grind)
            | exact resolve b4e66 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e67 (σ X0) (σ X1)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e67
            | exact resolve b4e67 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e67 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e278 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e100 X0 x
               have i₂ := b4e26 X0
               grind)
            | exact superpose b4e26 b4e100
            | (have j0 := b4e100 X0 y
               grind)
            | exact resolve b4e100 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e100
          have b4e302 : ∀ X0 : G, (M.op X0 y) = (k X0 x) ∨ (M.op x y) = X0 ∨ x = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e71 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e71
            | exact resolve b4e71 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e315 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = X0 ∨ (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (M.op X0 X1) = (M.op X1 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e46 X1 X2
               have i₂ := b4e71 X0 X1 X2
               grind)
            | (have i₁ := b4e46 X0 X1
               have i₂ := b4e71 (M.op (M.op X0 X1) X0) X1 X2
               grind)
            | exact superpose b4e71 b4e46
            | (have j1 := b4e71 X0 X1 X2
               grind)
            | exact resolve b4e46 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e71
          have b4e331 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e315 X0 X1 X2
               have j1 := b4e31 X0 X1 X2
               grind)
            | (have r₁ := b4e315 X0 X1 X2
               have r₂ := b4e31 X0 X1 X2
               grind)
            | (have r₁ := b4e315 X1 X0 X1
               have r₂ := b4e31 X0 X1 X0
               grind)
            | exact resolve b4e315 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e315
          have b4e378 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e56 X0 x
               have i₂ := b4e27 (σ X0)
               grind)
            | exact superpose b4e27 b4e56
            | (have j0 := b4e56 X0 x
               grind)
            | exact resolve b4e56 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e467 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e378 X0
               have i₂ := b4e27 (σ x)
               grind)
            | exact superpose b4e27 b4e378
            | (have j0 := b4e378 X0
               grind)
            | exact resolve b4e378 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e378
          have b4e1307 : ∀ X0 : G, (M.op X0 y) = (k X0 x) ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e331 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e331
            | exact resolve b4e331 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e331
          have b4e1380 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e27 (σ X0)
               have i₂ := b4e93 X0 x
               grind)
            | exact superpose b4e93 b4e27
            | (have j1 := b4e93 X0 x
               grind)
            | exact resolve b4e27 b4e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e93
          have b4e8921 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b4e467 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e467
          have b4e8923 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e8921
          have b4e52612 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1380 x
               grind)
            | exact superpose b4e1380 b4e20
            | (have j1 := b4e1380 x
               grind)
            | exact resolve b4e20 b4e1380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1380
          have b4e52800 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e52612
               have i₂ := b4e1307 x
               grind)
            | exact superpose b4e1307 b4e52612
            | (have j1 := b4e1307 x
               grind)
            | exact resolve b4e52612 b4e1307
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1307 b4e52612
          have b4e52807 : (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by grind
          clear b4e52800
          have b4e52838 : (M.op x y) = (τ (σ x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e52807
               grind)
            | exact superpose b4e52807 b4e14
            | exact resolve b4e14 b4e52807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52807
          have b4e52910 : x = (M.op x y) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e52838
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e52838
            | exact resolve b4e52838 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52838
          have b4e52922 : x = (k x x) := by
            first
            | (have j1 := b4e278 x
               grind)
            | (have r₁ := b4e52910
               have r₂ := b4e278 x
               grind)
            | exact resolve b4e52910 b4e278
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e278 b4e52910
          have b4e52982 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e8923
               have i₂ := b4e52922
               grind)
            | exact superpose b4e52922 b4e8923
            | exact resolve b4e8923 b4e52922
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8923
          have b4e52987 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e302 x
               have i₂ := b4e52922
               grind)
            | exact superpose b4e52922 b4e302
            | (have j0 := b4e302 x
               grind)
            | exact resolve b4e302 b4e52922
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e302 b4e52922
          have b4e53046 : x = (M.op x y) := by grind
          clear b4e52987
          have b4e53049 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e52982
          have b4e54081 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e53049
               grind)
            | exact superpose b4e53049 b4e20
            | exact resolve b4e20 b4e53049
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53049
          have b4e54213 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e54081
               have i₂ := b4e53046
               grind)
            | exact superpose b4e53046 b4e54081
            | exact resolve b4e54081 b4e53046
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53046 b4e54081
          have b4e54214 : False := by grind
          exact b4e54214
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
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
          have b5e28 : x ≠ y ∨ y = (k y y) := by
            first
            | (have i₁ := b5e16 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y y
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X0 (M.op X1 X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 X0 (M.op X1 X2)
               grind)
            | (have r₁ := b5e16 X0 (M.op X0 X0)
               have r₂ := b5e13 X0 X0 X0
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e38 : x = (k x y) ∨ y = (M.op x y) := by grind
          have b5e43 : x = (k x y) := by
            first
            | (have r₁ := b5e38
               have r₂ := b5e21
               grind)
            | exact resolve b5e38 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e55 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
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
          have b5e71 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e33 X1 X0
               grind)
            | exact superpose b5e33 b5e14
            | exact resolve b5e14 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e106 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e29 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e214 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e71 X0 (M.op (σ X0) (σ X0))
               have i₂ := b5e106 (σ X0)
               grind)
            | exact superpose b5e106 b5e71
            | exact resolve b5e71 b5e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71 b5e106
          have b5e222 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e214 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e214
            | exact resolve b5e214 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e214
          have b5e224 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e55 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e225 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e224
               have r₂ := b5e23
               grind)
            | exact resolve b5e224 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e224
          have b5e226 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e225
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e225
            | exact resolve b5e225 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e225
          have b5e227 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e226
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e226
            | exact resolve b5e226 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e226
          have b5e231 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e227
               grind)
            | exact superpose b5e227 b5e23
            | exact resolve b5e23 b5e227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e227
          have b5e323 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e48 y y
               grind)
            | exact superpose b5e48 b5e24
            | (have j1 := b5e48 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e48 x y
               grind)
            | exact resolve b5e24 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e364 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e323
          have b5e948 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e364
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e364
            | (have j1 := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e364 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e364
          have b5e949 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e948
          have b5e950 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e949
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e949
            | exact resolve b5e949 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e949
          have b5e951 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e950
          have b5e958 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e951
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e951
            | exact resolve b5e951 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e951
          have b5e1017 : y = (k y (τ (σ y))) ∨ x = y := by
            first
            | (have i₁ := b5e222 y
               have i₂ := b5e958
               grind)
            | exact superpose b5e958 b5e222
            | exact resolve b5e222 b5e958
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e222 b5e958
          have b5e1043 : y = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e1017
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e1017
            | exact resolve b5e1017 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1017
          have b5e1045 : y = (k y y) := by
            first
            | (have r₁ := b5e1043
               have r₂ := b5e28
               grind)
            | exact resolve b5e1043 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e1043
          have b5e1090 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e1045
               grind)
            | exact superpose b5e1045 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e1045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1045
          have b5e1091 : y = (M.op y y) := by grind
          clear b5e1090
          have b5e1160 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e1091
               grind)
            | exact superpose b5e1091 b5e22
            | exact resolve b5e22 b5e1091
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1091
          have b5e1243 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e231
               have i₂ := b5e1160
               grind)
            | exact superpose b5e1160 b5e231
            | exact resolve b5e231 b5e1160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e231 b5e1160
          have b5e1248 : False := by grind
          exact b5e1248
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e25 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e29 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e27
        have b6e30 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e29
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e29
          | exact resolve b6e29 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e31 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e30
             grind)
          | exact superpose b6e30 b6e13
          | exact resolve b6e13 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e32 : x = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e53 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e55 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e60 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e60 X0 X1
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e60 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e60 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e65 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e53
             have r₂ := b6e21
             grind)
          | exact resolve b6e53 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e72 : x = (M.op x y) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e20
             grind)
          | exact resolve b6e65 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e78 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e72
             grind)
          | exact superpose b6e72 b6e24
          | exact resolve b6e24 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e79 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e72
             grind)
          | exact superpose b6e72 b6e20
          | exact resolve b6e20 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e319 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e52 X0 x
             have i₂ := b6e25 (σ X0)
             grind)
          | exact superpose b6e25 b6e52
          | (have j0 := b6e52 X0 x
             grind)
          | exact resolve b6e52 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e402 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e319 X0
             have i₂ := b6e25 (σ x)
             grind)
          | exact superpose b6e25 b6e319
          | (have j0 := b6e319 X0
             grind)
          | exact resolve b6e319 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25 b6e319
        have b6e423 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e402 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e402
          | (have j0 := b6e402 X0
             grind)
          | exact resolve b6e402 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e402
        have b6e3511 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e423 x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e423
          | (have j0 := b6e423 (k x x)
             grind)
          | exact resolve b6e423 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e423
        have b6e3554 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e3511
        have b6e3563 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e3554
             have r₂ := b6e78
             grind)
          | exact resolve b6e3554 b6e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78 b6e3554
        have b6e3591 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e3563
             grind)
          | exact superpose b6e3563 b6e13
          | exact resolve b6e13 b6e3563
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3563
        have b6e3629 : y = (k x x) := by
          first
          | (have i₁ := b6e3591
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3591
          | exact resolve b6e3591 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3591
        have b6e3793 : y = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b6e63 x x
             have i₂ := b6e3629
             grind)
          | exact superpose b6e3629 b6e63
          | exact resolve b6e63 b6e3629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e3629
        have b6e3803 : y = (M.op x x) := by
          first
          | (have r₁ := b6e3793
             have r₂ := b6e79
             grind)
          | exact resolve b6e3793 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79 b6e3793
        have b6e3838 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x x
             have i₂ := b6e3803
             grind)
          | exact superpose b6e3803 b6e12
          | exact resolve b6e12 b6e3803
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4436 : y = (M.op x y) := by
          first
          | (have i₁ := b6e3803
             have i₂ := b6e3838 x
             grind)
          | exact superpose b6e3838 b6e3803
          | exact resolve b6e3803 b6e3838
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3803 b6e3838
        have b6e4493 : False := by grind
        exact b6e4493
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
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
          have b7e35 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b7e40 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e35
               have r₂ := b7e23
               grind)
            | exact resolve b7e35 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e41 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e40
            | exact resolve b7e40 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e44 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e41
               grind)
            | exact superpose b7e41 b7e14
            | exact resolve b7e14 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : x = (k x y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e44
            | exact resolve b7e44 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e55 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e61 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e64 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e61 X0 X1
               have j1 := b7e16 X0 X1
               grind)
            | (have r₁ := b7e61 X0 X1
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e61 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e74 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e75 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e22
               grind)
            | exact resolve b7e74 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e77 : x = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e21
               grind)
            | exact resolve b7e75 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e84 : x ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e21
            | exact resolve b7e21 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e359 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e53 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e53
            | exact resolve b7e53 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e434 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e359
          have b7e612 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e434
               grind)
            | exact superpose b7e434 b7e14
            | exact resolve b7e14 b7e434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e434
          have b7e627 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e612
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e612
            | exact resolve b7e612 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e612
          have b7e699 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e64 y y
               have i₂ := b7e627
               grind)
            | exact superpose b7e627 b7e64
            | exact resolve b7e64 b7e627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e627
          have b7e704 : x = y ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e699
               have r₂ := b7e22
               grind)
            | exact resolve b7e699 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e699
          have b7e711 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e704
               have r₂ := b7e84
               grind)
            | exact resolve b7e704 b7e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e704
          have b7e821 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e711
               grind)
            | exact superpose b7e711 b7e14
            | exact resolve b7e14 b7e711
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e711
          have b7e842 : x = y := by
            first
            | (have i₁ := b7e821
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e821
            | exact resolve b7e821 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e821
          have b7e849 : False := by grind
          exact b7e849
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
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
          have b8e212 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e55 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e213 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e212
               have r₂ := b8e23
               grind)
            | exact resolve b8e212 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212
          have b8e214 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e213
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e213
            | exact resolve b8e213 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e213
          have b8e217 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e214
               grind)
            | exact superpose b8e214 b8e20
            | exact resolve b8e20 b8e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e214
          have b8e451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e217
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e217
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e217 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e217
          have b8e452 : x = (M.op y y) ∨ y = (M.op x y) := by grind
          clear b8e451
          have b8e457 : y = (M.op x y) := by
            first
            | (have r₁ := b8e452
               have r₂ := b8e22
               grind)
            | exact resolve b8e452 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e452
          have b8e461 : False := by grind
          exact b8e461
