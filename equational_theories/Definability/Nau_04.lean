import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_x_pxx_pxy_Equation947 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e33 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ y) (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
           have i₂ := b0e11 X0 X2 X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
           have i₂ := b0e11 X0 X1 X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : x = (M.op y (M.op y y)) := by
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
      have b0e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e27 X0 X1
           have i₂ := b0e16 (τ X0) X1
           grind)
        | exact superpose b0e16 b0e27
        | (have j1 := b0e16 (τ X0) X1
           grind)
        | exact resolve b0e27 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e28 X1 X0
           grind)
        | exact superpose b0e28 b0e12
        | exact resolve b0e12 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e82 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) := by
        first
        | (have i₁ := b0e34 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e84 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (σ x))) = (M.op X0 (M.op (M.op X1 (M.op (σ y) (M.op X0 (σ x)))) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op (σ y) (M.op X0 (σ x))) X0 X1
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e182 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35 X0 X2 X2 X1
           have i₂ := b0e11 X0 X2 X1
           grind)
        | exact superpose b0e11 b0e35
        | exact resolve b0e35 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e210 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ y) (σ y))) (σ x)) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
        intro X0
        first
        | (have i₁ := b0e182 (M.op (σ y) (σ y)) X0 (σ y)
           have i₂ := b0e82
           grind)
        | exact superpose b0e82 b0e182
        | exact resolve b0e182 b0e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82
      have b0e212 : ∀ X0 : G, (M.op (M.op X0 (M.op y y)) x) = (M.op y (M.op (M.op y y) (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b0e182 (M.op y y) X0 y
           have i₂ := b0e40
           grind)
        | exact superpose b0e40 b0e182
        | exact resolve b0e182 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e216 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 x
           have i₂ := b0e182 X1 x X0
           grind)
        | exact superpose b0e182 b0e11
        | exact resolve b0e11 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e227 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y y)) x) := by
        intro X0
        first
        | (have i₁ := b0e212 X0
           have i₂ := b0e11 y y y
           grind)
        | exact superpose b0e11 b0e212
        | exact resolve b0e212 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e212
      have b0e228 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e210 X0
           have i₂ := b0e11 (σ y) (σ y) (σ y)
           grind)
        | exact superpose b0e11 b0e210
        | exact resolve b0e210 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e210
      have b0e318 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
           have i₂ := b0e38 X1 (M.op X2 X1) X3 X0
           grind)
        | exact superpose b0e38 b0e11
        | exact resolve b0e11 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e323 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e318 X1 x X2 X3
           have i₂ := b0e182 x X1 (M.op X2 x)
           grind)
        | exact superpose b0e182 b0e318
        | exact resolve b0e318 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318
      have b0e351 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
        intro X1 X3
        first
        | (have i₁ := b0e323 x X1 X3
           have i₂ := b0e182 x X1 x
           grind)
        | exact superpose b0e182 b0e323
        | exact resolve b0e323 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e323
      have b0e370 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
        intro X0
        first
        | (have i₁ := b0e216 (M.op X0 X0) (M.op X0 X0)
           have i₂ := b0e216 (M.op X0 X0) X0
           grind)
        | exact superpose b0e216 b0e216
        | exact resolve b0e216 b0e216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e377 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X1 X1 X0 X0
           have i₂ := b0e216 X1 (M.op X0 X1)
           grind)
        | exact superpose b0e216 b0e35
        | exact resolve b0e35 b0e216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e396 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e377 X0 X1
           have i₂ := b0e182 X1 X0 X0
           grind)
        | exact superpose b0e182 b0e377
        | exact resolve b0e377 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e377
      have b0e514 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X1 (M.op y y)) (M.op x x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e182 x X0 (M.op X1 (M.op y y))
           have i₂ := b0e227 X1
           grind)
        | exact superpose b0e227 b0e182
        | exact resolve b0e182 b0e227
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e182
      have b0e516 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op x (M.op (M.op X1 (M.op y y)) x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e514 X0 X1
           have i₂ := b0e396 (M.op X1 (M.op y y)) x
           grind)
        | exact superpose b0e396 b0e514
        | exact resolve b0e514 b0e396
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e514
      have b0e519 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) y) := by
        intro X0
        first
        | (have i₁ := b0e516 X0 x
           have i₂ := b0e227 x
           grind)
        | exact superpose b0e227 b0e516
        | exact resolve b0e516 b0e227
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e227 b0e516
      have b0e771 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X0) (M.op (M.op X1 (σ X2)) (σ X0))) ∨ (σ X0) = (M.op (σ X2) (σ X2)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (σ X2) (σ X0) X1
           have i₂ := b0e47 X2 X0
           grind)
        | exact superpose b0e47 b0e11
        | (have j1 := b0e47 X2 X0
           grind)
        | exact resolve b0e11 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e783 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e47 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e784 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e783 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e783
      have b0e1065 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e14 X0 (M.op X0 X0)
           have i₂ := b0e370 X0
           grind)
        | exact superpose b0e370 b0e14
        | (have j0 := b0e14 X0 (M.op X0 X0)
           grind)
        | (have r₁ := b0e14 X0 (M.op X0 X0)
           have r₂ := b0e370 X0
           grind)
        | exact resolve b0e14 b0e370
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e370
      have b0e1088 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
        intro X0
        first
        | (have j0 := b0e1065 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1065
      have b0e1177 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b0e70 X0 (M.op (σ X0) (σ X0))
           have i₂ := b0e1088 (σ X0)
           grind)
        | exact superpose b0e1088 b0e70
        | exact resolve b0e70 b0e1088
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70 b0e1088
      have b0e1181 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1177 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1177
        | exact resolve b0e1177 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1177
      have b0e1236 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e519 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e519
        | exact resolve b0e519 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e519
      have b0e1367 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e351 (M.op X1 X1) x
           have i₂ := b0e216 (M.op X1 X1) X1
           grind)
        | exact superpose b0e216 b0e351
        | exact resolve b0e351 b0e216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e351
      have b0e1491 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e1367 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e1367
        | exact resolve b0e1367 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1514 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X1 X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 (M.op X1 X0)
           have i₂ := b0e1367 X0 X1
           grind)
        | exact superpose b0e1367 b0e14
        | (have j0 := b0e14 X0 (M.op X1 X0)
           grind)
        | (have r₁ := b0e14 X0 (M.op X0 X0)
           have r₂ := b0e1367 X0 X0
           grind)
        | exact resolve b0e14 b0e1367
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1561 : (σ y) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e1491
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e1491
        | exact resolve b0e1491 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1491
      have b0e3052 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op (σ y) (σ y))) (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e84 (σ x) x
           have i₂ := b0e1561
           grind)
        | exact superpose b0e1561 b0e84
        | exact resolve b0e84 b0e1561
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84 b0e1561
      have b0e3110 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e3052 x
           have i₂ := b0e228 x
           grind)
        | exact superpose b0e228 b0e3052
        | exact resolve b0e3052 b0e228
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228 b0e3052
      have b0e3911 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e48 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e48
        | exact resolve b0e48 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e3978 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e3911 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e3911
        | (have j0 := b0e3911 X0 X1
           grind)
        | exact resolve b0e3911 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3911
      have b0e4847 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e216 X1 X0
           have i₂ := b0e396 X1 X0
           grind)
        | (have i₁ := b0e216 X1 X1
           have i₂ := b0e396 X1 X1
           grind)
        | exact superpose b0e396 b0e216
        | exact resolve b0e216 b0e396
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216 b0e396
      have b0e8060 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e3110
           grind)
        | exact superpose b0e3110 b0e18
        | exact resolve b0e18 b0e3110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3110
      have b0e8100 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e8060
           have i₂ := b0e1236
           grind)
        | exact superpose b0e1236 b0e8060
        | exact resolve b0e8060 b0e1236
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1236 b0e8060
      have b0e29113 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (M.op (σ X1) (M.op (M.op X2 X0) (σ X1))) = X0 ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e771 X0 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e771
        | exact resolve b0e771 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e771
      have b0e29439 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op X2 X0) (σ X1))) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e29113 X0 X1 X2
           have i₂ := b0e27 X0 X1
           grind)
        | exact superpose b0e27 b0e29113
        | (have j0 := b0e29113 X0 X1 X2
           grind)
        | exact resolve b0e29113 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e29113
      have b0e244546 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e1514 X0 X0
           have i₂ := b0e3978 X0 X1
           grind)
        | (have i₁ := b0e1514 X0 X1
           have i₂ := b0e3978 X0 (M.op X1 X0)
           grind)
        | exact superpose b0e3978 b0e1514
        | (have j1 := b0e3978 X1 X0
           grind)
        | (have r₁ := b0e1514 X0 X0
           have r₂ := b0e3978 X0 (M.op X0 X0)
           grind)
        | (have r₁ := b0e1514 X0 X1
           have r₂ := b0e3978 X0 (M.op X1 X0)
           grind)
        | (have r₁ := b0e1514 X0 (M.op X0 X0)
           have r₂ := b0e3978 X0 (M.op X0 X0)
           grind)
        | exact resolve b0e1514 b0e3978
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1514 b0e3978
      have b0e245002 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e244546 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e244546
      have b0e245166 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e245002 X0 X1
           have j1 := b0e14 X1 X0
           grind)
        | (have r₁ := b0e245002 X1 X0
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e245002 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e245002
      have b0e460396 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X0) = (σ X2) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e4847 (σ X2) (M.op X1 X0)
           have i₂ := b0e29439 X0 X2 X1
           grind)
        | exact superpose b0e29439 b0e4847
        | (have j1 := b0e29439 X0 X2 X2
           grind)
        | exact resolve b0e4847 b0e29439
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4847 b0e29439
      have b0e461442 : ∀ X0 X2 : G, (M.op X0 X0) = (σ X2) ∨ (M.op X0 X0) = (σ X2) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
        intro X0 X2
        first
        | (have i₁ := b0e460396 X0 x X2
           have i₂ := b0e1367 X0 x
           grind)
        | exact superpose b0e1367 b0e460396
        | (have j0 := b0e460396 X0 x X2
           grind)
        | exact resolve b0e460396 b0e1367
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1367 b0e460396
      have b0e461443 : ∀ X0 X2 : G, (M.op X0 X0) = (σ X2) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
        intro X0 X2
        first
        | (have j0 := b0e461442 X0 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e461442
      have b0e461500 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e461443 X0 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e461443
        | exact resolve b0e461443 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e461791 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1181 X1
           have i₂ := b0e461443 (σ X1) X0
           grind)
        | exact superpose b0e461443 b0e1181
        | (have j1 := b0e461443 (σ X1) X0
           grind)
        | exact resolve b0e1181 b0e461443
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1181 b0e461443
      have b0e461896 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e461791 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e461791
        | (have j0 := b0e461791 X0 X1
           grind)
        | exact resolve b0e461791 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e461791
      have b0e461945 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e461896 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e461896
        | (have j0 := b0e461896 X0 X1
           grind)
        | exact resolve b0e461896 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e461896
      have b0e783774 : (σ (k y y)) ≠ (σ (M.op y y)) ∨ y = (k y y) := by
        first
        | (have i₁ := b0e8100
           have i₂ := b0e461945 y y
           grind)
        | exact superpose b0e461945 b0e8100
        | (have j1 := b0e461945 y y
           grind)
        | exact resolve b0e8100 b0e461945
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e461945
      have b0e783846 : y = (k y y) := by
        first
        | (have j1 := b0e245166 y y
           grind)
        | (have r₁ := b0e783774
           have r₂ := b0e245166 y y
           grind)
        | exact resolve b0e783774 b0e245166
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e245166 b0e783774
      have b0e784711 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e784 y
           have i₂ := b0e783846
           grind)
        | exact superpose b0e783846 b0e784
        | (have j0 := b0e784 y
           grind)
        | exact resolve b0e784 b0e783846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e784
      have b0e784726 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e461500 y y
           have i₂ := b0e783846
           grind)
        | exact superpose b0e783846 b0e461500
        | (have j0 := b0e461500 y y
           grind)
        | exact resolve b0e461500 b0e783846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e461500 b0e783846
      have b0e784727 : y = (M.op y y) := by grind
      clear b0e784726
      have b0e784735 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b0e784711
      have b0e800088 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e8100
           have i₂ := b0e784735
           grind)
        | exact superpose b0e784735 b0e8100
        | exact resolve b0e8100 b0e784735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8100 b0e784735
      have b0e800436 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e800088
           have i₂ := b0e784727
           grind)
        | exact superpose b0e784727 b0e800088
        | exact resolve b0e800088 b0e784727
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e784727 b0e800088
      have b0e800437 : False := by grind
      exact b0e800437
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y ≠ y ∨ x = (k x y) := by
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
        have b1e26 : x = (k x y) := by grind
        clear b1e24
        have b1e55 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e58 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e55
             have r₂ := b1e21
             grind)
          | exact resolve b1e55 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e59 : (σ y) = (σ (k x y)) := by
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
        have b1e60 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e59
          | exact resolve b1e59 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e59
        have b1e62 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e22
          | exact resolve b1e22 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e21
          | exact resolve b1e21 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e70 : False := by grind
        exact b1e70
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y ≠ y ∨ x = (k x y) := by
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
        have b2e25 : x = (k x y) := by grind
        clear b2e24
        have b2e28 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
          intro X0
          first
          | (have i₁ := b2e12 x X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
             have i₂ := b2e12 X0 X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
             have i₂ := b2e12 X0 X1 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : x = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b2e28 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e28
          | exact resolve b2e28 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e46 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e91 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e46 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e92 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e91
             have r₂ := b2e21
             grind)
          | exact resolve b2e91 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e93 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e92
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e92
          | exact resolve b2e92 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92
        have b2e94 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e93
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e93
          | exact resolve b2e93 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e93
        have b2e95 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e94
             grind)
          | exact superpose b2e94 b2e19
          | exact resolve b2e19 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e131 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 X0 X2 X2 X1
             have i₂ := b2e12 X0 X2 X1
             grind)
          | exact superpose b2e12 b2e29
          | exact resolve b2e29 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e172 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
             have i₂ := b2e31 X1 (M.op X2 X1) X3 X0
             grind)
          | exact superpose b2e31 b2e12
          | exact resolve b2e12 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e175 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
          intro X1 X2 X3
          first
          | (have i₁ := b2e172 X1 x X2 X3
             have i₂ := b2e131 x X1 (M.op X2 x)
             grind)
          | exact superpose b2e131 b2e172
          | exact resolve b2e172 b2e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e172
        have b2e189 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
          intro X1 X3
          first
          | (have i₁ := b2e175 x X1 X3
             have i₂ := b2e131 x X1 x
             grind)
          | exact superpose b2e131 b2e175
          | exact resolve b2e175 b2e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e175
        have b2e425 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e41 x x
             grind)
          | exact superpose b2e41 b2e22
          | (have j1 := b2e41 x x
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e41 x y
             grind)
          | exact resolve b2e22 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e478 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e425
        have b2e619 : ∀ X0 : G, (M.op (M.op X0 (M.op y y)) x) = (M.op y (M.op (M.op y y) (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b2e131 (M.op y y) X0 y
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e131
          | exact resolve b2e131 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e626 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 x
             have i₂ := b2e131 X1 x X0
             grind)
          | exact superpose b2e131 b2e12
          | exact resolve b2e12 b2e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e131
        have b2e650 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y y)) x) := by
          intro X0
          first
          | (have i₁ := b2e619 X0
             have i₂ := b2e12 y y y
             grind)
          | exact superpose b2e12 b2e619
          | exact resolve b2e619 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e619
        have b2e787 : y = (M.op x x) := by
          first
          | (have i₁ := b2e650 y
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e650
          | exact resolve b2e650 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e650
        have b2e1183 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e189 (M.op X1 X1) x
             have i₂ := b2e626 (M.op X1 X1) X1
             grind)
          | exact superpose b2e626 b2e189
          | exact resolve b2e189 b2e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e189
        have b2e1374 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e478
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e478
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e478 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478
        have b2e1376 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1374
        have b2e1379 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1376
             have i₂ := b2e787
             grind)
          | exact superpose b2e787 b2e1376
          | exact resolve b2e1376 b2e787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1376
        have b2e1380 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1379
        have b2e1382 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e1380
             have i₂ := b2e787
             grind)
          | exact superpose b2e787 b2e1380
          | exact resolve b2e1380 b2e787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1380
        have b2e1860 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1183 (σ y) (σ x)
             have i₂ := b2e94
             grind)
          | exact superpose b2e94 b2e1183
          | exact resolve b2e1183 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1183
        have b2e1938 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1860
             have i₂ := b2e94
             grind)
          | exact superpose b2e94 b2e1860
          | exact resolve b2e1860 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94 b2e1860
        have b2e2159 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b2e626 X0 (σ y)
             have i₂ := b2e1938
             grind)
          | exact superpose b2e1938 b2e626
          | exact resolve b2e626 b2e1938
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e626 b2e1938
        have b2e4653 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e2159 (σ x)
             have i₂ := b2e1382
             grind)
          | exact superpose b2e1382 b2e2159
          | exact resolve b2e2159 b2e1382
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1382 b2e2159
        have b2e4692 : x = y := by
          first
          | (have r₁ := b2e4653
             have r₂ := b2e22
             grind)
          | exact resolve b2e4653 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4653
        have b2e4798 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e95
             have i₂ := b2e4692
             grind)
          | exact superpose b2e4692 b2e95
          | exact resolve b2e95 b2e4692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e4816 : y = (M.op y y) := by
          first
          | (have i₁ := b2e787
             have i₂ := b2e4692
             grind)
          | exact superpose b2e4692 b2e787
          | exact resolve b2e787 b2e4692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e787 b2e4692
        have b2e4840 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e4798
             have i₂ := b2e4816
             grind)
          | exact superpose b2e4816 b2e4798
          | exact resolve b2e4798 b2e4816
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4798 b2e4816
        have b2e4841 : False := by grind
        exact b2e4841
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e25
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
        have b3e28 : (k x y) = (τ (σ x)) := by
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
        have b3e29 : x = (k x y) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e28
          | exact resolve b3e28 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e61 : y = (k x y) ∨ y = (M.op y x) := by grind
        have b3e64 : y = (k x y) := by
          first
          | (have r₁ := b3e61
             have r₂ := b3e20
             grind)
          | exact resolve b3e61 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e67 : x = y := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e64
             grind)
          | exact superpose b3e64 b3e29
          | exact resolve b3e29 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e64
        have b3e79 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e67
             grind)
          | exact superpose b3e67 b3e20
          | exact resolve b3e20 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e80 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e67
             grind)
          | exact superpose b3e67 b3e21
          | exact resolve b3e21 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e90 : False := by grind
        exact b3e90
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e35 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b4e35 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e56 : ∀ X0 : G, (M.op y y) = (M.op x (M.op (M.op X0 (M.op y y)) x)) := by
            intro X0
            first
            | (have i₁ := b4e13 (M.op y y) x X0
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e13
            | exact resolve b4e13 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : y = (k x y) ∨ y = (M.op y x) := by grind
          have b4e66 : y = (k x y) := by
            first
            | (have r₁ := b4e60
               have r₂ := b4e21
               grind)
            | exact resolve b4e60 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e165 : (M.op y y) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b4e56 x
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e56
            | exact resolve b4e56 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e170 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e165
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e165
            | exact resolve b4e165 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e165
          have b4e176 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b4e13 y y X0
               have i₂ := b4e170
               grind)
            | exact superpose b4e170 b4e13
            | exact resolve b4e13 b4e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e170
          have b4e214 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e37 X0 X2 X2 X1
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e37
            | exact resolve b4e37 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e677 : ∀ X0 : G, y ≠ y ∨ (M.op (M.op X0 y) (M.op x y)) = (k (M.op (M.op X0 y) (M.op x y)) y) := by
            intro X0
            first
            | (have i₁ := b4e16 (M.op (M.op X0 y) (M.op x y)) y
               have i₂ := b4e176 X0
               grind)
            | exact superpose b4e176 b4e16
            | (have j0 := b4e16 (M.op (M.op X0 y) (M.op x y)) y
               grind)
            | (have r₁ := b4e16 (M.op (M.op X0 y) (M.op x y)) y
               have r₂ := b4e176 X0
               grind)
            | exact resolve b4e16 b4e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e176
          have b4e685 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (k (M.op (M.op X0 y) (M.op x y)) y) := by
            intro X0
            first
            | (have j0 := b4e677 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e677
          have b4e690 : (M.op x (M.op y y)) = (k (M.op x (M.op y y)) y) := by
            first
            | (have i₁ := b4e685 x
               have i₂ := b4e214 y x x
               grind)
            | exact superpose b4e214 b4e685
            | exact resolve b4e685 b4e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214 b4e685
          have b4e697 : x = (k x y) := by
            first
            | (have i₁ := b4e690
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e690
            | exact resolve b4e690 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e690
          have b4e758 : x = y := by
            first
            | (have i₁ := b4e66
               have i₂ := b4e697
               grind)
            | exact superpose b4e697 b4e66
            | exact resolve b4e66 b4e697
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66 b4e697
          have b4e797 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e758
               grind)
            | exact superpose b4e758 b4e23
            | exact resolve b4e23 b4e758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e828 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b4e797
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e797
            | exact resolve b4e797 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e797
          have b4e839 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e828
               have i₂ := b4e758
               grind)
            | exact superpose b4e758 b4e828
            | exact resolve b4e828 b4e758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e758 b4e828
          have b4e840 : False := by grind
          exact b4e840
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e33 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e33 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e157 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X2 X2 X1
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e34
            | exact resolve b5e34 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e617 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e157 x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e157
            | exact resolve b5e157 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e726 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e617 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e617
            | exact resolve b5e617 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e617
          have b5e790 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b5e13 y y X0
               have i₂ := b5e726
               grind)
            | exact superpose b5e726 b5e13
            | exact resolve b5e13 b5e726
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e726
          have b5e804 : y = (M.op y (M.op x (M.op y y))) := by
            first
            | (have i₁ := b5e790 x
               have i₂ := b5e157 y x x
               grind)
            | exact superpose b5e157 b5e790
            | exact resolve b5e790 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e157 b5e790
          have b5e807 : y = (M.op y x) := by
            first
            | (have i₁ := b5e804
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e804
            | exact resolve b5e804 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e804
          have b5e809 : False := by grind
          exact b5e809
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e24
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
        have b6e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
             have i₂ := b6e12 X0 X2 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
             have i₂ := b6e12 X0 X1 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e58 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e65 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e58
             have r₂ := b6e21
             grind)
          | exact resolve b6e58 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e68 : x = (M.op x y) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e20
             grind)
          | exact resolve b6e65 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e157 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e40 X0 X2 X2 X1
             have i₂ := b6e12 X0 X2 X1
             grind)
          | exact superpose b6e12 b6e40
          | exact resolve b6e40 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e212 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
             have i₂ := b6e42 X1 (M.op X2 X1) X3 X0
             grind)
          | exact superpose b6e42 b6e12
          | exact resolve b6e12 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e227 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
          intro X1 X2 X3
          first
          | (have i₁ := b6e212 X1 x X2 X3
             have i₂ := b6e157 x X1 (M.op X2 x)
             grind)
          | exact superpose b6e157 b6e212
          | exact resolve b6e212 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e212
        have b6e237 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
          intro X1 X3
          first
          | (have i₁ := b6e227 x X1 X3
             have i₂ := b6e157 x X1 x
             grind)
          | exact superpose b6e157 b6e227
          | exact resolve b6e227 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e227
        have b6e626 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 x
             have i₂ := b6e157 X1 x X0
             grind)
          | exact superpose b6e157 b6e12
          | exact resolve b6e12 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e157
        have b6e747 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e626 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b6e626 (M.op X0 X0) X0
             grind)
          | exact superpose b6e626 b6e626
          | exact resolve b6e626 b6e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e829 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (M.op X0 X0)
             have i₂ := b6e747 X0
             grind)
          | exact superpose b6e747 b6e15
          | (have j0 := b6e15 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b6e15 X0 (M.op X0 X0)
             have r₂ := b6e747 X0
             grind)
          | exact resolve b6e15 b6e747
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e747
        have b6e848 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e829 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e829
        have b6e920 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e848 X1
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e848 X0
             have i₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e17 b6e848
          | (have j1 := b6e17 X1 X0
             grind)
          | exact resolve b6e848 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e848
        have b6e941 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e920 X0 X1
             have j1 := b6e15 X1 X0
             grind)
          | (have r₁ := b6e920 X1 X0
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e920 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e920
        have b6e1182 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e237 (M.op X1 X1) x
             have i₂ := b6e626 (M.op X1 X1) X1
             grind)
          | exact superpose b6e626 b6e237
          | exact resolve b6e237 b6e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e237 b6e626
        have b6e1866 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e1182 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1182
          | exact resolve b6e1182 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1182
        have b6e1939 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e1866
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1866
          | exact resolve b6e1866 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1866
        have b6e2084 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e56 x x
             have i₂ := b6e1939
             grind)
          | exact superpose b6e1939 b6e56
          | exact resolve b6e56 b6e1939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56 b6e1939
        have b6e2113 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e2084
        have b6e34973 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e2113
             grind)
          | exact superpose b6e2113 b6e13
          | exact resolve b6e13 b6e2113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2113
        have b6e35066 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e34973
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e34973
          | exact resolve b6e34973 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34973
        have b6e35633 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e941 x x
             have i₂ := b6e35066
             grind)
          | exact superpose b6e35066 b6e941
          | exact resolve b6e941 b6e35066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e941 b6e35066
        have b6e35641 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b6e35633
             have r₂ := b6e21
             grind)
          | exact resolve b6e35633 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35633
        have b6e36137 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e35641
             grind)
          | exact superpose b6e35641 b6e13
          | exact resolve b6e13 b6e35641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35641
        have b6e36225 : x = y ∨ x = y := by
          first
          | (have i₁ := b6e36137
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e36137
          | exact resolve b6e36137 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36137
        have b6e36226 : x = y := by grind
        clear b6e36225
        have b6e36742 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e36226
             grind)
          | exact superpose b6e36226 b6e21
          | exact resolve b6e21 b6e36226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36749 : y = (M.op y y) := by
          first
          | (have i₁ := b6e68
             have i₂ := b6e36226
             grind)
          | exact superpose b6e36226 b6e68
          | exact resolve b6e68 b6e36226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68 b6e36226
        have b6e36852 : False := by grind
        exact b6e36852
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e46 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
            | (have r₁ := b7e16 X0 (M.op X0 X0)
               have r₂ := b7e18 X0 (M.op (M.op X0 X0) X0)
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          have b7e62 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e23
               grind)
            | exact resolve b7e58 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e63 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e62
            | exact resolve b7e62 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e67 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e14
            | exact resolve b7e14 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e68 : y = (k x y) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e67
            | exact resolve b7e67 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e74 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e75 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e22
               grind)
            | exact resolve b7e74 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e77 : y = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e21
               grind)
            | exact resolve b7e75 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e84 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b7e13 y x X0
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e13
            | exact resolve b7e13 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e116 : y = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b7e84 x
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e84
            | exact resolve b7e84 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e124 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e46 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e124 X0
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e124 X0
               have r₂ := b7e16 X0 X0
               grind)
            | exact resolve b7e124 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e124
          have b7e151 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e31 X0 X2 X2 X1
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e31
            | exact resolve b7e31 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e498 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
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
          have b7e568 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e498
          have b7e610 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e568
               grind)
            | exact superpose b7e568 b7e14
            | exact resolve b7e14 b7e568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e568
          have b7e625 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e610
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e610
            | exact resolve b7e610 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e610
          have b7e667 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e125 x
               have i₂ := b7e625
               grind)
            | exact superpose b7e625 b7e125
            | exact resolve b7e125 b7e625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125 b7e625
          have b7e678 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e667
               have r₂ := b7e22
               grind)
            | exact resolve b7e667 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e667
          have b7e717 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op x (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b7e151 y X0 x
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e151
            | exact resolve b7e151 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e750 : ∀ X0 : G, y = (M.op (M.op X0 y) y) := by
            intro X0
            first
            | (have i₁ := b7e717 X0
               have i₂ := b7e116
               grind)
            | exact superpose b7e116 b7e717
            | exact resolve b7e717 b7e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116 b7e717
          have b7e812 : y = (M.op y y) := by
            first
            | (have i₁ := b7e750 x
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e750
            | exact resolve b7e750 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e750
          have b7e1039 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e678
               grind)
            | exact superpose b7e678 b7e14
            | exact resolve b7e14 b7e678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e678
          have b7e1069 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e1039
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1039
            | exact resolve b7e1039 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1039
          have b7e1070 : x = y := by grind
          clear b7e1069
          have b7e1137 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e1070
               grind)
            | exact superpose b7e1070 b7e21
            | exact resolve b7e21 b7e1070
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1152 : x = (M.op x x) := by
            first
            | (have i₁ := b7e812
               have i₂ := b7e1070
               grind)
            | exact superpose b7e1070 b7e812
            | exact resolve b7e812 b7e1070
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e812 b7e1070
          have b7e1160 : False := by grind
          exact b7e1160
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e43 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e89 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e43 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e90 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e89
               have r₂ := b8e23
               grind)
            | exact resolve b8e89 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e91 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e90
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e90
            | exact resolve b8e90 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e92 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e91
               grind)
            | exact superpose b8e91 b8e20
            | exact resolve b8e20 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e99 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e92
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e92
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e92 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e100 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e99
          have b8e102 : y = (M.op y x) := by
            first
            | (have r₁ := b8e100
               have r₂ := b8e22
               grind)
            | exact resolve b8e100 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100
          have b8e104 : False := by grind
          exact b8e104

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op x x) := by grind
        have b0e21 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e22 : y = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e41 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 x X0 X1
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e42 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) y)) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 y X0 X1
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e44 : x = y := by
          first
          | (have i₁ := b0e41 x x
             have i₂ := b0e42 x x
             grind)
          | exact superpose b0e42 b0e41
          | exact resolve b0e41 b0e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e42
        have b0e45 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e44
             grind)
          | exact superpose b0e44 b0e19
          | exact resolve b0e19 b0e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e47 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e44
             grind)
          | exact superpose b0e44 b0e21
          | exact resolve b0e21 b0e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e44
        have b0e49 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e45
             have i₂ := b0e47
             grind)
          | exact superpose b0e47 b0e45
          | exact resolve b0e45 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e45 b0e47
        have b0e50 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e49
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e49
          | exact resolve b0e49 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e49
        have b0e51 : False := by grind
        exact b0e51
      · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
        · have b1e23 : y ≠ (M.op y y) := by grind
          have b1e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : False := by grind
          exact b1e26
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op x x) := by grind
          have b2e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b2e24 : y ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e31 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13 X0 x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e32 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13 X0 (σ x) (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
               have i₂ := b2e13 X0 X2 X1
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e34 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 x X0 X1
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e35 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 X0) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 (σ x) X0 X1
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e36 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
               have i₂ := b2e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e37 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b2e31 x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e31
            | exact resolve b2e31 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e38 : (σ x) = (M.op x (M.op y (σ y))) := by
            first
            | (have i₁ := b2e31 (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e31
            | exact resolve b2e31 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e39 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b2e31 (M.op y y)
               have i₂ := b2e13 y y y
               grind)
            | exact superpose b2e13 b2e31
            | exact resolve b2e31 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e40 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 (M.op y (M.op X0 X0)) x
               have i₂ := b2e31 X0
               grind)
            | exact superpose b2e31 b2e13
            | exact resolve b2e13 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 X0
               have i₂ := b2e18 (σ X1) (σ X0)
               grind)
            | exact superpose b2e18 b2e19
            | (have j1 := b2e18 (σ X1) (σ X0)
               grind)
            | exact resolve b2e19 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e68 : x = (M.op (M.op y y) (M.op x y)) := by
            first
            | (have i₁ := b2e34 (M.op y y) x
               have i₂ := b2e37
               grind)
            | exact superpose b2e37 b2e34
            | exact resolve b2e34 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e34 b2e37
          have b2e77 : x = (M.op (M.op y y) (M.op y y)) := by
            first
            | (have i₁ := b2e68
               have i₂ := b2e39
               grind)
            | exact superpose b2e39 b2e68
            | exact resolve b2e68 b2e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e68
          have b2e78 : x = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b2e77
               have i₂ := b2e36 y y
               grind)
            | exact superpose b2e36 b2e77
            | exact resolve b2e77 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e77
          have b2e109 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b2e32 (M.op (σ y) (σ y))
               have i₂ := b2e13 (σ y) (σ y) (σ y)
               grind)
            | exact superpose b2e13 b2e32
            | exact resolve b2e32 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e127 : ∀ X0 : G, (σ x) = (M.op (M.op y (M.op X0 X0)) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b2e35 (M.op y (M.op X0 X0)) x
               have i₂ := b2e31 X0
               grind)
            | exact superpose b2e31 b2e35
            | exact resolve b2e35 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e161 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13 X0 X0 X0
               have i₂ := b2e36 X0 X0
               grind)
            | exact superpose b2e36 b2e13
            | exact resolve b2e13 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e162 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ x) (M.op (σ y) (M.op X0 (M.op X1 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b2e32 (M.op X1 X0)
               have i₂ := b2e36 X1 X0
               grind)
            | exact superpose b2e36 b2e32
            | exact resolve b2e32 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e164 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x (M.op y (M.op X0 (M.op X1 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b2e31 (M.op X1 X0)
               have i₂ := b2e36 X1 X0
               grind)
            | exact superpose b2e36 b2e31
            | exact resolve b2e31 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e165 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 (M.op X1 X0) X2 X3
               have i₂ := b2e36 X1 X0
               grind)
            | exact superpose b2e36 b2e13
            | exact resolve b2e13 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e200 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e33 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
               have i₂ := b2e33 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b2e33 b2e33
            | exact resolve b2e33 b2e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e208 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e33 X4 X2 X3 (M.op X1 X0)
               have i₂ := b2e36 X1 X0
               grind)
            | exact superpose b2e36 b2e33
            | exact resolve b2e33 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e209 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e33 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
               have i₂ := b2e33 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b2e33 b2e33
            | exact resolve b2e33 b2e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e222 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
               have i₂ := b2e33 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b2e33 b2e13
            | exact resolve b2e13 b2e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e225 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op x (M.op y (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e31 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
               have i₂ := b2e33 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b2e33 b2e31
            | exact resolve b2e31 b2e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e226 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ x) (M.op (σ y) (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e32 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
               have i₂ := b2e33 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b2e33 b2e32
            | exact resolve b2e32 b2e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e32
          have b2e227 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
            intro X0 X3
            first
            | (have i₁ := b2e36 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
               have i₂ := b2e33 X0 x x X3
               grind)
            | exact superpose b2e33 b2e36
            | exact resolve b2e36 b2e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e228 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b2e35 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
               have i₂ := b2e33 X1 x x X0
               grind)
            | exact superpose b2e33 b2e35
            | exact resolve b2e35 b2e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e231 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b2e13 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
               have i₂ := b2e33 X1 x x X0
               grind)
            | exact superpose b2e33 b2e13
            | exact resolve b2e13 b2e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e233 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e226 X0 X1
               have i₂ := b2e36 X0 X1
               grind)
            | exact superpose b2e36 b2e226
            | exact resolve b2e226 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e226
          have b2e234 : ∀ X0 X1 : G, (M.op x (M.op y (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e225 X0 X1
               have i₂ := b2e36 X0 X1
               grind)
            | exact superpose b2e36 b2e225
            | exact resolve b2e225 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e225
          have b2e237 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e222 X0 X1 X2 X3
               have i₂ := b2e36 X0 X1
               grind)
            | exact superpose b2e36 b2e222
            | exact resolve b2e222 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e222
          have b2e243 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e209 X0 X1 X2 X3 X4
               have i₂ := b2e36 X0 X1
               grind)
            | exact superpose b2e36 b2e209
            | exact resolve b2e209 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e209
          have b2e244 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e200 X0 X1 X2 X3 X4
               have i₂ := b2e36 X0 X1
               grind)
            | exact superpose b2e36 b2e200
            | exact resolve b2e200 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e200
          have b2e247 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op x (M.op y (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e237 X0 X1 X2 X3
               have i₂ := b2e234 X0 X1
               grind)
            | exact superpose b2e234 b2e237
            | exact resolve b2e237 b2e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e237
          have b2e252 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (σ x) (M.op (σ y) (M.op X0 X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e243 X0 X1 X2 X3 X4
               have i₂ := b2e233 X0 X1
               grind)
            | exact superpose b2e233 b2e243
            | exact resolve b2e243 b2e233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e243
          have b2e253 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (σ x) (M.op (σ y) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e244 X0 X1 X2 X3 X4
               have i₂ := b2e233 X0 X1
               grind)
            | exact superpose b2e233 b2e244
            | exact resolve b2e244 b2e233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e233 b2e244
          have b2e281 : y = (M.op y x) := by
            first
            | (have i₁ := b2e161 y
               have i₂ := b2e78
               grind)
            | exact superpose b2e78 b2e161
            | exact resolve b2e161 b2e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e78
          have b2e559 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e161 (σ X0)
               have i₂ := b2e56 X0 X0
               grind)
            | exact superpose b2e56 b2e161
            | (have j1 := b2e56 X0 X0
               grind)
            | exact resolve b2e161 b2e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e161
          have b2e580 : ∀ X0 X1 : G, (σ X1) = (M.op x (M.op y (σ X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e31 (σ X1)
               have i₂ := b2e56 X0 X1
               grind)
            | exact superpose b2e56 b2e31
            | (have j1 := b2e56 X0 X1
               grind)
            | exact resolve b2e31 b2e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e56
          have b2e609 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b2e559 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e559
          have b2e907 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e109
               grind)
            | exact superpose b2e109 b2e20
            | exact resolve b2e20 b2e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e918 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b2e907
               have i₂ := b2e39
               grind)
            | exact superpose b2e39 b2e907
            | exact resolve b2e907 b2e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e907
          have b2e2002 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b2e35 (M.op X0 (σ y)) (M.op y (M.op X0 X0))
               have i₂ := b2e127 X0
               grind)
            | exact superpose b2e127 b2e35
            | exact resolve b2e35 b2e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e35 b2e127
          have b2e2013 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have i₁ := b2e2002 X0
               have i₂ := b2e109
               grind)
            | exact superpose b2e109 b2e2002
            | exact resolve b2e2002 b2e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e109 b2e2002
          have b2e2388 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e164 (M.op X0 X0) (M.op X1 (M.op X0 X0))
               have i₂ := b2e13 X0 (M.op X0 X0) X1
               grind)
            | exact superpose b2e13 b2e164
            | exact resolve b2e164 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2795 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e231 (M.op X0 (M.op X0 X0)) X1 X2
               have i₂ := b2e231 X0 X0 X0
               grind)
            | exact superpose b2e231 b2e231
            | exact resolve b2e231 b2e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2884 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X0 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 (M.op X0 (M.op X0 X0)) X1 X2
               have i₂ := b2e231 X0 X0 X0
               grind)
            | exact superpose b2e231 b2e13
            | exact resolve b2e13 b2e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2887 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b2e31 (M.op X0 (M.op X0 X0))
               have i₂ := b2e231 X0 X0 X0
               grind)
            | exact superpose b2e231 b2e31
            | exact resolve b2e31 b2e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31
          have b2e2890 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e33 X3 X1 X2 (M.op X0 (M.op X0 X0))
               have i₂ := b2e231 X0 X0 X0
               grind)
            | exact superpose b2e231 b2e33
            | exact resolve b2e33 b2e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e33
          have b2e2892 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op y (M.op X1 X1)) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e40 X1 (M.op X0 (M.op X0 X0))
               have i₂ := b2e231 X0 X0 X0
               grind)
            | exact superpose b2e231 b2e40
            | exact resolve b2e40 b2e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2905 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e227 (M.op x (M.op x x)) x
               have i₂ := b2e231 x x x
               grind)
            | exact superpose b2e231 b2e227
            | exact resolve b2e227 b2e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e3423 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e231 X0 X0 X1
               have i₂ := b2e2887 X0
               grind)
            | exact superpose b2e2887 b2e231
            | exact resolve b2e231 b2e2887
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e231
          have b2e3446 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op x (M.op y (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 (M.op X0 X1) X1 X0
               have i₂ := b2e2887 (M.op X0 X1)
               grind)
            | exact superpose b2e2887 b2e13
            | exact resolve b2e13 b2e2887
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e3919 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op x (M.op y X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e2905 X0 X1
               have i₂ := b2e2887 X0
               grind)
            | exact superpose b2e2887 b2e2905
            | exact resolve b2e2905 b2e2887
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2887
          have b2e4915 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e162 (M.op X0 X0) (M.op X1 (M.op X0 X0))
               have i₂ := b2e13 X0 (M.op X0 X0) X1
               grind)
            | exact superpose b2e13 b2e162
            | exact resolve b2e162 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e162
          have b2e4969 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b2e4915 X0 x
               have i₂ := b2e2388 X0 x
               grind)
            | exact superpose b2e2388 b2e4915
            | exact resolve b2e4915 b2e2388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e4915
          have b2e5256 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e165 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X2 X3
               have i₂ := b2e13 X0 (M.op X0 X0) X1
               grind)
            | exact superpose b2e13 b2e165
            | exact resolve b2e165 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e165
          have b2e5366 : ∀ X0 X2 X3 : G, (M.op x (M.op y X0)) = (M.op X2 (M.op (M.op X3 X2) X0)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b2e5256 X0 x X2 X3
               have i₂ := b2e2388 X0 x
               grind)
            | exact superpose b2e2388 b2e5256
            | exact resolve b2e5256 b2e2388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2388 b2e5256
          have b2e6780 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x (M.op y (M.op X1 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b2e247 X1 (M.op X0 X0) (M.op X1 X1) y
               have i₂ := b2e40 X1 X0
               grind)
            | exact superpose b2e40 b2e247
            | exact resolve b2e247 b2e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e40
          have b2e9543 : ∀ X0 X1 X2 : G, (M.op x (M.op y (M.op X2 (M.op X1 (M.op X0 X1))))) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e247 X2 (M.op X1 (M.op X0 X1)) (M.op X2 X2) (M.op x x)
               have i₂ := b2e208 X1 X0 x x X2
               grind)
            | exact superpose b2e208 b2e247
            | exact resolve b2e247 b2e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e208 b2e247
          have b2e15721 : ∀ X0 X1 : G, (M.op x (M.op y (M.op X0 X1))) = (M.op (M.op (σ x) (M.op (σ y) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e164 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (σ x) (M.op (σ y) (M.op X0 X1)))
               have i₂ := b2e253 X0 X1 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b2e253 b2e164
            | exact resolve b2e164 b2e253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e164 b2e253
          have b2e15886 : ∀ X0 X1 : G, (M.op x (M.op y (M.op X0 X1))) = (M.op (M.op (σ x) (M.op (σ y) (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e15721 X0 X1
               have i₂ := b2e36 X0 X1
               grind)
            | exact superpose b2e36 b2e15721
            | exact resolve b2e15721 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e15721
          have b2e16103 : ∀ X0 X1 : G, (M.op x (M.op y (M.op X0 X1))) = (M.op (M.op x (M.op y (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e15886 X0 X1
               have i₂ := b2e4969 (M.op X0 X1)
               grind)
            | exact superpose b2e4969 b2e15886
            | exact resolve b2e15886 b2e4969
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e15886
          have b2e28089 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) (M.op X0 (M.op X0 X0))) = (M.op x (M.op y (M.op (M.op X1 X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b2e234 (M.op X1 X0) X0
               have i₂ := b2e2884 X0 X0 X1
               grind)
            | exact superpose b2e2884 b2e234
            | exact resolve b2e234 b2e2884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e234 b2e2884
          have b2e28423 : ∀ X0 X1 : G, (M.op x (M.op y (M.op (M.op X1 X0) X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e28089 X0 X1
               have i₂ := b2e2905 X0 (M.op X1 X0)
               grind)
            | exact superpose b2e2905 b2e28089
            | exact resolve b2e28089 b2e2905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e28089
          have b2e45247 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (M.op (σ X0) (σ X0))) (σ X0)) ∨ (σ X0) = (M.op x (M.op y (σ y))) ∨ (M.op (σ y) (σ X0)) = (σ (k X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e228 (σ X0) X1
               have i₂ := b2e580 y X0
               grind)
            | exact superpose b2e580 b2e228
            | (have j1 := b2e580 y X0
               grind)
            | exact resolve b2e228 b2e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e228 b2e580
          have b2e45358 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op x (M.op y (σ y))) ∨ (M.op (σ y) (σ X0)) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b2e45247 X0 x
               have i₂ := b2e227 (σ X0) x
               grind)
            | exact superpose b2e227 b2e45247
            | (have j0 := b2e45247 X0 x
               grind)
            | exact resolve b2e45247 b2e227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e227 b2e45247
          have b2e45449 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k X0 y)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b2e45358 X0
               have i₂ := b2e38
               grind)
            | exact superpose b2e38 b2e45358
            | (have j0 := b2e45358 X0
               grind)
            | exact resolve b2e45358 b2e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e38 b2e45358
          have b2e73092 : ∀ X0 X1 : G, (M.op x (M.op y (M.op X1 (M.op X0 X0)))) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e5366 (M.op X1 (M.op X0 X0)) (M.op y X1) x
               have i₂ := b2e3423 X1 X0
               grind)
            | exact superpose b2e3423 b2e5366
            | exact resolve b2e5366 b2e3423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e73112 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (σ y) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op x (M.op y X3)) (M.op x (M.op y X3)))) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e252 X3 (M.op X0 X0) X1 X2 (M.op x (M.op y X3))
               have i₂ := b2e3423 X3 X0
               grind)
            | exact superpose b2e3423 b2e252
            | exact resolve b2e252 b2e3423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3423
          have b2e73230 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (σ y) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op y X3) (M.op x (M.op y X3)))) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e73112 X0 X1 X2 X3
               have i₂ := b2e36 x (M.op y X3)
               grind)
            | exact superpose b2e36 b2e73112
            | exact resolve b2e73112 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73112
          have b2e73369 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (σ y) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) X3) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e73230 X0 X1 X2 X3
               have i₂ := b2e3919 X3 y
               grind)
            | exact superpose b2e3919 b2e73230
            | exact resolve b2e73230 b2e3919
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3919 b2e73230
          have b2e73414 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op y (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) X3) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e73369 X0 X1 X2 X3
               have i₂ := b2e4969 (M.op X3 (M.op X0 X0))
               grind)
            | exact superpose b2e4969 b2e73369
            | exact resolve b2e73369 b2e4969
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73369
          have b2e73433 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y X3) X0) = (M.op (M.op (M.op X1 X2) X3) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e73414 X0 X1 X2 X3
               have i₂ := b2e73092 X0 X3
               grind)
            | exact superpose b2e73092 b2e73414
            | exact resolve b2e73414 b2e73092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73414
          have b2e178157 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x (M.op y (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b2e5366 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) X1 x
               have i₂ := b2e2795 X1 x X0
               grind)
            | exact superpose b2e2795 b2e5366
            | exact resolve b2e5366 b2e2795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e5366
          have b2e178189 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X3 X4) (M.op X3 X4))) X0) = (M.op (σ x) (M.op (σ y) (M.op (M.op X4 (M.op X4 X4)) (M.op X0 X0)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e252 (M.op X4 (M.op X4 X4)) (M.op X0 X0) X1 X2 (M.op X3 X4)
               have i₂ := b2e2795 X4 X3 X0
               grind)
            | exact superpose b2e2795 b2e252
            | exact resolve b2e252 b2e2795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e252 b2e2795
          have b2e178362 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X3 X4) (M.op X3 X4))) X0) = (M.op x (M.op y (M.op (M.op X4 (M.op X4 X4)) (M.op X0 X0)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e178189 X0 X1 X2 X3 X4
               have i₂ := b2e4969 (M.op (M.op X4 (M.op X4 X4)) (M.op X0 X0))
               grind)
            | exact superpose b2e4969 b2e178189
            | exact resolve b2e178189 b2e4969
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e4969 b2e178189
          have b2e178378 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op y (M.op X1 (M.op X1 X1))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e178157 X0 X1
               have i₂ := b2e73092 X0 (M.op X1 (M.op X1 X1))
               grind)
            | exact superpose b2e73092 b2e178157
            | exact resolve b2e178157 b2e73092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e178157
          have b2e178675 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y (M.op X4 (M.op X4 X4))) X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X3 X4) (M.op X3 X4))) X0) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e178362 X0 X1 X2 X3 X4
               have i₂ := b2e73092 X0 (M.op X4 (M.op X4 X4))
               grind)
            | exact superpose b2e73092 b2e178362
            | exact resolve b2e178362 b2e73092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73092 b2e178362
          have b2e178858 : ∀ X0 X3 X4 : G, (M.op (M.op y (M.op X4 (M.op X4 X4))) X0) = (M.op (M.op y (M.op (M.op X3 X4) (M.op X3 X4))) X0) := by
            intro X0 X3 X4
            first
            | (have i₁ := b2e178675 X0 x x X3 X4
               have i₂ := b2e73433 X0 x x (M.op (M.op X3 X4) (M.op X3 X4))
               grind)
            | exact superpose b2e73433 b2e178675
            | exact resolve b2e178675 b2e73433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73433 b2e178675
          have b2e178966 : ∀ X0 X3 X4 : G, (M.op (M.op y (M.op X4 (M.op X4 X4))) X0) = (M.op (M.op y (M.op X4 (M.op X3 X4))) X0) := by
            intro X0 X3 X4
            first
            | (have i₁ := b2e178858 X0 X3 X4
               have i₂ := b2e36 X3 X4
               grind)
            | exact superpose b2e36 b2e178858
            | exact resolve b2e178858 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e178858
          have b2e179019 : ∀ X0 X3 X4 : G, (M.op X4 X0) = (M.op (M.op y (M.op X4 (M.op X3 X4))) X0) := by
            intro X0 X3 X4
            first
            | (have i₁ := b2e178966 X0 X3 X4
               have i₂ := b2e178378 X0 X4
               grind)
            | exact superpose b2e178378 b2e178966
            | exact resolve b2e178966 b2e178378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e178378 b2e178966
          have b2e192043 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op y (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e179019 X2 (M.op y (M.op X1 X1)) (M.op X1 X0)
               have i₂ := b2e2892 X0 X1
               grind)
            | exact superpose b2e2892 b2e179019
            | exact resolve b2e179019 b2e2892
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2892
          have b2e192371 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op y (M.op X0 (M.op X0 (M.op X1 X0))))) := by
            intro X0 X1
            first
            | (have i₁ := b2e28423 (M.op X0 (M.op X1 X0)) y
               have i₂ := b2e179019 (M.op X0 (M.op X1 X0)) X1 X0
               grind)
            | exact superpose b2e179019 b2e28423
            | exact resolve b2e28423 b2e179019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e28423 b2e179019
          have b2e192874 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e192371 X0 X1
               have i₂ := b2e9543 X1 X0 X0
               grind)
            | exact superpose b2e9543 b2e192371
            | exact resolve b2e192371 b2e9543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e9543 b2e192371
          have b2e192991 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e192043 X0 X1 X2
               have i₂ := b2e2905 X0 X1
               grind)
            | exact superpose b2e2905 b2e192043
            | exact resolve b2e192043 b2e2905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192043
          have b2e196688 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e3446 X0 (M.op X1 X1)
               have i₂ := b2e6780 X1 X0
               grind)
            | exact superpose b2e6780 b2e3446
            | exact resolve b2e3446 b2e6780
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3446 b2e6780
          have b2e196844 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e196688 X0 X1
               have i₂ := b2e192874 X1 (M.op X0 X0)
               grind)
            | exact superpose b2e192874 b2e196688
            | exact resolve b2e196688 b2e192874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192874 b2e196688
          have b2e201876 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e192991 X1 X0 X2
               have i₂ := b2e192991 X1 X3 X2
               grind)
            | (have i₁ := b2e192991 X0 X1 X2
               have i₂ := b2e192991 X0 y X2
               grind)
            | exact superpose b2e192991 b2e192991
            | exact resolve b2e192991 b2e192991
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192991
          have b2e309293 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b2e196844 (M.op X1 X1) (M.op X1 X0)
               have i₂ := b2e2890 X0 X1 X1 X1
               grind)
            | exact superpose b2e2890 b2e196844
            | exact resolve b2e196844 b2e2890
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2890 b2e196844
          have b2e310100 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b2e309293 X0 X1
               have i₂ := b2e36 X1 X0
               grind)
            | exact superpose b2e36 b2e309293
            | exact resolve b2e309293 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36 b2e309293
          have b2e310315 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e310100 X0 X1
               have i₂ := b2e2905 X0 X1
               grind)
            | exact superpose b2e2905 b2e310100
            | exact resolve b2e310100 b2e2905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2905 b2e310100
          have b2e311042 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e201876 X1 X2 (M.op X0 (M.op X2 X0)) X2
               have i₂ := b2e310315 X0 X2
               grind)
            | exact superpose b2e310315 b2e201876
            | exact resolve b2e201876 b2e310315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e201876 b2e310315
          have b2e396648 : ∀ X0 : G, (M.op X0 (M.op X0 (σ (k (τ X0) (τ X0))))) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e609 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e609
            | exact resolve b2e609 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e609
          have b2e396771 : ∀ X0 : G, (M.op X0 (M.op X0 (k (σ (τ X0)) X0))) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e396648 X0
               have i₂ := b2e30 X0 (τ X0)
               grind)
            | exact superpose b2e30 b2e396648
            | (have j0 := b2e396648 X0
               grind)
            | exact resolve b2e396648 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30 b2e396648
          have b2e396779 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e396771 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e396771
            | (have j0 := b2e396771 X0
               grind)
            | exact resolve b2e396771 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e396771
          have b2e521863 : (M.op x y) = (M.op (M.op x y) (M.op (k y y) (M.op y (k y y)))) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b2e16103 y (k y y)
               have i₂ := b2e396779 y
               grind)
            | exact superpose b2e396779 b2e16103
            | (have j1 := b2e396779 y
               grind)
            | exact resolve b2e16103 b2e396779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e16103 b2e396779
          have b2e521925 : (M.op x y) = (M.op (M.op x y) (M.op (k y y) (M.op y (k y y)))) := by
            first
            | (have r₁ := b2e521863
               have r₂ := b2e24
               grind)
            | exact resolve b2e521863 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e521863
          have b2e522011 : (M.op x y) = (k y y) := by
            first
            | (have i₁ := b2e521925
               have i₂ := b2e311042 (k y y) x y
               grind)
            | exact superpose b2e311042 b2e521925
            | exact resolve b2e521925 b2e311042
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e311042 b2e521925
          have b2e522061 : (M.op y y) = (k y y) := by
            first
            | (have i₁ := b2e522011
               have i₂ := b2e39
               grind)
            | exact superpose b2e39 b2e522011
            | exact resolve b2e522011 b2e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e39 b2e522011
          have b2e607935 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e918
               have i₂ := b2e45449 y
               grind)
            | exact superpose b2e45449 b2e918
            | (have j1 := b2e45449 y
               grind)
            | exact resolve b2e918 b2e45449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e918 b2e45449
          have b2e607951 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e607935
               have i₂ := b2e522061
               grind)
            | exact superpose b2e522061 b2e607935
            | exact resolve b2e607935 b2e522061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e522061 b2e607935
          have b2e607952 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b2e607951
          have b2e608010 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e2013 (σ y)
               have i₂ := b2e607952
               grind)
            | exact superpose b2e607952 b2e2013
            | exact resolve b2e2013 b2e607952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2013 b2e607952
          have b2e608632 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e608010
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e608010
            | exact resolve b2e608010 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e608010
          have b2e608633 : (σ x) = (σ y) := by grind
          clear b2e608632
          have b2e609029 : x = (τ (σ y)) := by
            first
            | (have i₁ := b2e14 x
               have i₂ := b2e608633
               grind)
            | exact superpose b2e608633 b2e14
            | exact resolve b2e14 b2e608633
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e608633
          have b2e609112 : x = y := by
            first
            | (have i₁ := b2e609029
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e609029
            | exact resolve b2e609029 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e609029
          have b2e609353 : y = (M.op y y) := by
            first
            | (have i₁ := b2e281
               have i₂ := b2e609112
               grind)
            | exact superpose b2e609112 b2e281
            | exact resolve b2e281 b2e609112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e281 b2e609112
          have b2e610000 : False := by grind
          exact b2e610000
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op x x) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ y)) := by grind
          have b3e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e33 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b3e13 X0 x x
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e13
            | exact resolve b3e13 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e38 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b3e33 x
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e33
            | exact resolve b3e33 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33
          have b3e44 : x = (M.op x y) := by
            first
            | (have i₁ := b3e38
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e38
            | exact resolve b3e38 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e38
          have b3e74 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e26
               have i₂ := b3e44
               grind)
            | exact superpose b3e44 b3e26
            | exact resolve b3e26 b3e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e44
          have b3e78 : False := by grind
          exact b3e78
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b4e25 : y ≠ (M.op y y) := by grind
            have b4e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : False := by grind
            exact b4e28
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op x x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b5e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
            have b5e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b5e20 X1 (τ X0)
                 have i₂ := b5e16 X0
                 grind)
              | exact superpose b5e16 b5e20
              | exact resolve b5e20 b5e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e38 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b5e14 X0 x x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e39 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b5e14 X0 (σ y) (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e14
              | exact resolve b5e14 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e41 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 x X0 X1
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e42 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
                 have i₂ := b5e14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e43 : x = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b5e38 x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e38
              | exact resolve b5e38 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e44 : (M.op x y) = (M.op y y) := by
              first
              | (have i₁ := b5e38 (M.op y y)
                 have i₂ := b5e14 y y y
                 grind)
              | exact superpose b5e14 b5e38
              | exact resolve b5e38 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e38
            have b5e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b5e20 X1 X0
                 have i₂ := b5e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b5e19 b5e20
              | (have j1 := b5e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b5e20 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e77 : x = (M.op (M.op y y) (M.op x y)) := by
              first
              | (have i₁ := b5e41 (M.op y y) x
                 have i₂ := b5e43
                 grind)
              | exact superpose b5e43 b5e41
              | exact resolve b5e41 b5e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e41 b5e43
            have b5e86 : x = (M.op (M.op y y) (M.op y y)) := by
              first
              | (have i₁ := b5e77
                 have i₂ := b5e44
                 grind)
              | exact superpose b5e44 b5e77
              | exact resolve b5e77 b5e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e44 b5e77
            have b5e87 : x = (M.op y (M.op y y)) := by
              first
              | (have i₁ := b5e86
                 have i₂ := b5e42 y y
                 grind)
              | exact superpose b5e42 b5e86
              | exact resolve b5e86 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e86
            have b5e96 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b5e15 (k X0 (τ X1))
                 have i₂ := b5e31 X1 X0
                 grind)
              | exact superpose b5e31 b5e15
              | exact resolve b5e15 b5e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31
            have b5e101 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b5e39 (M.op (σ x) (σ x))
                 have i₂ := b5e14 (σ x) (σ x) (σ x)
                 grind)
              | exact superpose b5e14 b5e39
              | exact resolve b5e39 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e39
            have b5e122 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b5e14 X0 X0 X0
                 have i₂ := b5e42 X0 X0
                 grind)
              | exact superpose b5e42 b5e14
              | exact resolve b5e14 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e42
            have b5e236 : y = (M.op y x) := by
              first
              | (have i₁ := b5e122 y
                 have i₂ := b5e87
                 grind)
              | exact superpose b5e87 b5e122
              | exact resolve b5e122 b5e87
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e87 b5e122
            have b5e449 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e62 x x
                 grind)
              | exact superpose b5e62 b5e23
              | (have j1 := b5e62 x x
                 grind)
              | (have r₁ := b5e23
                 have r₂ := b5e62 y x
                 grind)
              | exact resolve b5e23 b5e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e62
            have b5e516 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b5e449
            have b5e529 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b5e516
                 have i₂ := b5e101
                 grind)
              | exact superpose b5e101 b5e516
              | exact resolve b5e516 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e516
            have b5e608 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
              intro X0
              grind
            clear b5e96
            have b5e625 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b5e608 X0
                 have i₂ := b5e15 X0
                 grind)
              | exact superpose b5e15 b5e608
              | exact resolve b5e608 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e608
            have b5e1154 : x = (k x (τ (M.op (σ y) (σ x)))) := by
              first
              | (have i₁ := b5e625 x
                 have i₂ := b5e101
                 grind)
              | exact superpose b5e101 b5e625
              | exact resolve b5e625 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e101 b5e625
            have b5e3912 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b5e529
                 have i₂ := b5e19 x x
                 grind)
              | exact superpose b5e19 b5e529
              | (have j1 := b5e19 x x
                 grind)
              | exact resolve b5e529 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e529
            have b5e3913 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
            clear b5e3912
            have b5e3914 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b5e3913
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e3913
              | exact resolve b5e3913 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3913
            have b5e3915 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
            clear b5e3914
            have b5e3921 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
              first
              | (have i₁ := b5e3915
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e3915
              | exact resolve b5e3915 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3915
            have b5e4086 : x = (k x (τ (σ x))) ∨ x = y := by
              first
              | (have i₁ := b5e1154
                 have i₂ := b5e3921
                 grind)
              | exact superpose b5e3921 b5e1154
              | exact resolve b5e1154 b5e3921
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1154 b5e3921
            have b5e4110 : x = (k x x) ∨ x = y := by
              first
              | (have i₁ := b5e4086
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e4086
              | exact resolve b5e4086 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e4086
            have b5e4579 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
              first
              | (have i₁ := b5e19 x x
                 have i₂ := b5e4110
                 grind)
              | exact superpose b5e4110 b5e19
              | (have j0 := b5e19 x x
                 grind)
              | exact resolve b5e19 b5e4110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e4110
            have b5e4580 : x = (M.op x x) ∨ x = y := by grind
            clear b5e4579
            have b5e4589 : x = y ∨ x = y := by
              first
              | (have i₁ := b5e4580
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e4580
              | exact resolve b5e4580 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e4580
            have b5e4590 : x = y := by grind
            clear b5e4589
            have b5e4658 : y = (M.op y y) := by
              first
              | (have i₁ := b5e236
                 have i₂ := b5e4590
                 grind)
              | exact superpose b5e4590 b5e236
              | exact resolve b5e236 b5e4590
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e236 b5e4590
            have b5e4679 : False := by grind
            exact b5e4679
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op x x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e27 : y = (k y y) := by grind
          have b6e30 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b6e13 X0 x x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e36 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b6e30 x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e30
            | exact resolve b6e30 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b6e30 (M.op y y)
               have i₂ := b6e13 y y y
               grind)
            | exact superpose b6e13 b6e30
            | exact resolve b6e30 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30
          have b6e40 : y = (M.op x y) := by
            first
            | (have i₁ := b6e38
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e38
            | exact resolve b6e38 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38
          have b6e42 : x = (M.op x y) := by
            first
            | (have i₁ := b6e36
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e36
            | exact resolve b6e36 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e36
          have b6e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b6e22
               have i₂ := b6e18 (σ x) X0
               grind)
            | (have i₁ := b6e22
               have i₂ := b6e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b6e18 b6e22
            | (have j1 := b6e18 (σ x) X0
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e22 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e66 : x = y := by
            first
            | (have i₁ := b6e40
               have i₂ := b6e42
               grind)
            | exact superpose b6e42 b6e40
            | exact resolve b6e40 b6e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e40 b6e42
          have b6e85 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e66
               grind)
            | exact superpose b6e66 b6e23
            | exact resolve b6e23 b6e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e88 : x = (k x x) := by
            first
            | (have i₁ := b6e27
               have i₂ := b6e66
               grind)
            | exact superpose b6e66 b6e27
            | exact resolve b6e27 b6e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e27
          have b6e401 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b6e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e62
          have b6e402 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b6e401
               have r₂ := b6e23
               grind)
            | exact resolve b6e401 b6e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e401
          have b6e403 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b6e402
               have i₂ := b6e66
               grind)
            | exact superpose b6e66 b6e402
            | exact resolve b6e402 b6e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e66 b6e402
          have b6e404 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
            first
            | (have i₁ := b6e403
               have i₂ := b6e19 x x
               grind)
            | exact superpose b6e19 b6e403
            | exact resolve b6e403 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e403
          have b6e405 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e404
               have i₂ := b6e88
               grind)
            | exact superpose b6e88 b6e404
            | exact resolve b6e404 b6e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e88 b6e404
          have b6e406 : False := by grind
          exact b6e406
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b7e25 : y ≠ (M.op y y) := by grind
            have b7e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : False := by grind
            exact b7e28
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b8e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op x x) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 (τ X0)
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e37 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b8e14 X0 x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e39 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 x X0 X1
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
                 have i₂ := b8e14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e41 : x = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b8e37 x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e37
              | exact resolve b8e37 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e42 : (M.op x y) = (M.op y y) := by
              first
              | (have i₁ := b8e37 (M.op y y)
                 have i₂ := b8e14 y y y
                 grind)
              | exact superpose b8e14 b8e37
              | exact resolve b8e37 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e37
            have b8e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 X0
                 have i₂ := b8e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b8e19 b8e20
              | (have j1 := b8e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b8e20 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e70 : x = (M.op (M.op y y) (M.op x y)) := by
              first
              | (have i₁ := b8e39 (M.op y y) x
                 have i₂ := b8e41
                 grind)
              | exact superpose b8e41 b8e39
              | exact resolve b8e39 b8e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e39 b8e41
            have b8e78 : x = (M.op (M.op y y) (M.op y y)) := by
              first
              | (have i₁ := b8e70
                 have i₂ := b8e42
                 grind)
              | exact superpose b8e42 b8e70
              | exact resolve b8e70 b8e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e42 b8e70
            have b8e79 : x = (M.op y (M.op y y)) := by
              first
              | (have i₁ := b8e78
                 have i₂ := b8e40 y y
                 grind)
              | exact superpose b8e40 b8e78
              | exact resolve b8e78 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e78
            have b8e88 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e15 (k X0 (τ X1))
                 have i₂ := b8e30 X1 X0
                 grind)
              | exact superpose b8e30 b8e15
              | exact resolve b8e15 b8e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e30
            have b8e106 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b8e14 X0 X0 X0
                 have i₂ := b8e40 X0 X0
                 grind)
              | exact superpose b8e40 b8e14
              | exact resolve b8e14 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e40
            have b8e189 : y = (M.op y x) := by
              first
              | (have i₁ := b8e106 y
                 have i₂ := b8e79
                 grind)
              | exact superpose b8e79 b8e106
              | exact resolve b8e106 b8e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e79 b8e106
            have b8e419 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e56 x x
                 grind)
              | exact superpose b8e56 b8e23
              | (have j1 := b8e56 x x
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e56 y x
                 grind)
              | exact resolve b8e23 b8e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e56
            have b8e484 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b8e419
            have b8e578 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
              intro X0
              grind
            clear b8e88
            have b8e595 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b8e578 X0
                 have i₂ := b8e15 X0
                 grind)
              | exact superpose b8e15 b8e578
              | exact resolve b8e578 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e578
            have b8e2780 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b8e484
                 have i₂ := b8e19 x x
                 grind)
              | exact superpose b8e19 b8e484
              | (have j1 := b8e19 (σ x) (σ x)
                 grind)
              | exact resolve b8e484 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e484
            have b8e2781 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
            clear b8e2780
            have b8e2782 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b8e2781
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e2781
              | exact resolve b8e2781 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2781
            have b8e2783 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
            clear b8e2782
            have b8e2789 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
              first
              | (have i₁ := b8e2783
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e2783
              | exact resolve b8e2783 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2783
            have b8e3429 : x = (k x (τ (σ x))) ∨ x = y := by
              first
              | (have i₁ := b8e595 x
                 have i₂ := b8e2789
                 grind)
              | exact superpose b8e2789 b8e595
              | exact resolve b8e595 b8e2789
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e595 b8e2789
            have b8e3489 : x = (k x x) ∨ x = y := by
              first
              | (have i₁ := b8e3429
                 have i₂ := b8e15 x
                 grind)
              | exact superpose b8e15 b8e3429
              | exact resolve b8e3429 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3429
            have b8e3582 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
              first
              | (have i₁ := b8e19 x x
                 have i₂ := b8e3489
                 grind)
              | exact superpose b8e3489 b8e19
              | (have j0 := b8e19 x x
                 grind)
              | exact resolve b8e19 b8e3489
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3489
            have b8e3583 : x = (M.op x x) ∨ x = y := by grind
            clear b8e3582
            have b8e3592 : x = y ∨ x = y := by
              first
              | (have i₁ := b8e3583
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e3583
              | exact resolve b8e3583 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3583
            have b8e3593 : x = y := by grind
            clear b8e3592
            have b8e3792 : y = (M.op y y) := by
              first
              | (have i₁ := b8e189
                 have i₂ := b8e3593
                 grind)
              | exact superpose b8e3593 b8e189
              | exact resolve b8e189 b8e3593
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e189 b8e3593
            have b8e3813 : False := by grind
            exact b8e3813
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b9e21 : y ≠ (M.op x x) := by grind
          have b9e22 : x = (M.op x y) := by grind
          have b9e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e44 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b9e13 X0 y x
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e51 : y = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b9e44 y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e44
            | exact resolve b9e44 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e53 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b9e44 (M.op x x)
               have i₂ := b9e13 x x x
               grind)
            | exact superpose b9e13 b9e44
            | exact resolve b9e44 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e44
          have b9e55 : y = (M.op y x) := by
            first
            | (have i₁ := b9e51
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e51
            | exact resolve b9e51 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e51
          have b9e86 : y = (M.op x x) := by
            first
            | (have i₁ := b9e55
               have i₂ := b9e53
               grind)
            | exact superpose b9e53 b9e55
            | exact resolve b9e55 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e53 b9e55
          have b9e89 : False := by grind
          exact b9e89
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b10e25 : y ≠ (M.op y y) := by grind
            have b10e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e28 : False := by grind
            exact b10e28
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b11e22 : y ≠ (M.op x x) := by grind
            have b11e23 : x = (M.op x y) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b11e21
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e21
              | exact resolve b11e21 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e39 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b11e14 X0 y x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e45 : (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b11e39 (M.op x x)
                 have i₂ := b11e14 x x x
                 grind)
              | exact superpose b11e14 b11e39
              | exact resolve b11e39 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e39
            have b11e55 : x = (k x (M.op y x)) := by grind
            have b11e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b11e20 X1 X0
                 have i₂ := b11e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b11e19 b11e20
              | (have j1 := b11e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b11e20 b11e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e535 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b11e64 x x
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e64
              | exact resolve b11e64 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e64
            have b11e615 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
            clear b11e535
            have b11e967 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b11e15 (k x x)
                 have i₂ := b11e615
                 grind)
              | exact superpose b11e615 b11e15
              | exact resolve b11e15 b11e615
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e983 : y = (k x x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b11e967
                 have i₂ := b11e15 y
                 grind)
              | exact superpose b11e15 b11e967
              | exact resolve b11e967 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e967
            have b11e999 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b11e19 x x
                 have i₂ := b11e983
                 grind)
              | exact superpose b11e983 b11e19
              | (have j0 := b11e19 x x
                 grind)
              | exact resolve b11e19 b11e983
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e983
            have b11e1000 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
            clear b11e999
            have b11e1002 : x = (M.op x x) ∨ (σ x) = (σ y) := by
              first
              | (have r₁ := b11e1000
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e1000 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1000
            have b11e1010 : x = (M.op y x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b11e1002
                 have i₂ := b11e45
                 grind)
              | exact superpose b11e45 b11e1002
              | exact resolve b11e1002 b11e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e45 b11e1002
            have b11e1136 : x = (k x x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b11e55
                 have i₂ := b11e1010
                 grind)
              | exact superpose b11e1010 b11e55
              | exact resolve b11e55 b11e1010
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e55 b11e1010
            have b11e1307 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b11e615
                 have i₂ := b11e1136
                 grind)
              | exact superpose b11e1136 b11e615
              | exact resolve b11e615 b11e1136
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e615 b11e1136
            have b11e1314 : (σ x) = (σ y) := by grind
            clear b11e1307
            have b11e1401 : (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b11e24
                 have i₂ := b11e1314
                 grind)
              | exact superpose b11e1314 b11e24
              | exact resolve b11e24 b11e1314
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e1402 : (σ y) ≠ (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b11e28
                 have i₂ := b11e1314
                 grind)
              | exact superpose b11e1314 b11e28
              | exact resolve b11e28 b11e1314
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e28 b11e1314
            have b11e1425 : False := by grind
            exact b11e1425
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : x = (M.op x y) := by grind
            have b12e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e21
              | exact resolve b12e21 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e29 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e28
              | exact resolve b12e28 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28
            have b12e30 : False := by grind
            exact b12e30
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b13e27 : y ≠ (M.op y y) := by grind
              have b13e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : False := by grind
              exact b13e30
            · have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : x = (M.op x y) := by grind
              have b14e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e30 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e22
                | exact resolve b14e22 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e31 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b14e30
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e30
                | exact resolve b14e30 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e30
              have b14e32 : False := by grind
              exact b14e32
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e22 : y ≠ (M.op x x) := by grind
            have b15e23 : x = (M.op x y) := by grind
            have b15e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e38 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b15e14 X0 y x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e43 : y = (M.op y (M.op x y)) := by
              first
              | (have i₁ := b15e38 y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e38
              | exact resolve b15e38 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e44 : (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b15e38 (M.op x x)
                 have i₂ := b15e14 x x x
                 grind)
              | exact superpose b15e14 b15e38
              | exact resolve b15e38 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e38
            have b15e46 : y = (M.op y x) := by
              first
              | (have i₁ := b15e43
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e43
              | exact resolve b15e43 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e43
            have b15e81 : y = (M.op x x) := by
              first
              | (have i₁ := b15e46
                 have i₂ := b15e44
                 grind)
              | exact superpose b15e44 b15e46
              | exact resolve b15e46 b15e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e44 b15e46
            have b15e84 : False := by grind
            exact b15e84
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b16e27 : y ≠ (M.op y y) := by grind
              have b16e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : False := by grind
              exact b16e30
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op x x) := by grind
              have b17e24 : x = (M.op x y) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e28 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X1 (τ X0)
                   have i₂ := b17e17 X0
                   grind)
                | exact superpose b17e17 b17e21
                | exact resolve b17e21 b17e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e33 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b17e15 X0 y x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
                   have i₂ := b17e15 X0 X2 X1
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
                   have i₂ := b17e15 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e36 : (M.op x x) = (M.op y x) := by
                first
                | (have i₁ := b17e33 (M.op x x)
                   have i₂ := b17e15 x x x
                   grind)
                | exact superpose b17e15 b17e33
                | exact resolve b17e33 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e38 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
                first
                | (have i₁ := b17e19 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x y
                   grind)
                | (have r₁ := b17e19 x y
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e41 : y = (M.op x x) ∨ x = (k x y) := by grind
              clear b17e38
              have b17e42 : x = (k x y) := by
                first
                | (have r₁ := b17e41
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e41 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e41
              have b17e46 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X1 X0
                   have i₂ := b17e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b17e25
                   have i₂ := b17e20 (σ x) X0
                   grind)
                | (have i₁ := b17e25
                   have i₂ := b17e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b17e20 b17e25
                | (have j1 := b17e20 (σ x) X0
                   grind)
                | (have r₁ := b17e25
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e25 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e55 : y ≠ (M.op y x) := by
                first
                | (have i₁ := b17e23
                   have i₂ := b17e36
                   grind)
                | exact superpose b17e36 b17e23
                | exact resolve b17e23 b17e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36
              have b17e74 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e16 (k X0 (τ X1))
                   have i₂ := b17e32 X1 X0
                   grind)
                | exact superpose b17e32 b17e16
                | exact resolve b17e16 b17e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e32
              have b17e86 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b17e15 X0 X0 X0
                   have i₂ := b17e35 X0 X0
                   grind)
                | exact superpose b17e35 b17e15
                | exact resolve b17e15 b17e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e88 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op x (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b17e33 (M.op X1 X0)
                   have i₂ := b17e35 X1 X0
                   grind)
                | exact superpose b17e35 b17e33
                | exact resolve b17e33 b17e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35
              have b17e93 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e86 X1
                   have i₂ := b17e20 X1 X0
                   grind)
                | (have i₁ := b17e86 X0
                   have i₂ := b17e20 X0 (M.op X0 X0)
                   grind)
                | exact superpose b17e20 b17e86
                | (have j1 := b17e20 X1 X0
                   grind)
                | exact resolve b17e86 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e135 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
                intro X0 X1 X4
                first
                | (have i₁ := b17e15 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
                   have i₂ := b17e34 X1 x x X0
                   grind)
                | exact superpose b17e34 b17e15
                | exact resolve b17e15 b17e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e34
              have b17e185 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b17e54 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e54
              have b17e186 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b17e185
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e185 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e185
              have b17e187 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e186
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e186
                | exact resolve b17e186 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e186
              have b17e188 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e187
                   have i₂ := b17e42
                   grind)
                | exact superpose b17e42 b17e187
                | exact resolve b17e187 b17e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e42 b17e187
              have b17e308 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
                intro X0
                grind
              clear b17e74
              have b17e323 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b17e308 X0
                   have i₂ := b17e16 X0
                   grind)
                | exact superpose b17e16 b17e308
                | exact resolve b17e308 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e308
              have b17e400 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b17e86 (σ X0)
                   have i₂ := b17e46 X0 X0
                   grind)
                | exact superpose b17e46 b17e86
                | (have j1 := b17e46 X0 X0
                   grind)
                | exact resolve b17e86 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e86
              have b17e436 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b17e46 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46
              have b17e437 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b17e436 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e436
              have b17e441 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b17e400 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e400
              have b17e1161 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op X0 (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e33 (M.op X0 (M.op X0 X0))
                   have i₂ := b17e135 X0 X0 X0
                   grind)
                | exact superpose b17e135 b17e33
                | exact resolve b17e33 b17e135
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e33 b17e135
              have b17e1499 : (M.op x y) = (M.op y (M.op x (M.op y (M.op y y)))) := by
                first
                | (have i₁ := b17e88 y x
                   have i₂ := b17e1161 y
                   grind)
                | exact superpose b17e1161 b17e88
                | exact resolve b17e88 b17e1161
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1161
              have b17e1544 : (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b17e1499
                   have i₂ := b17e88 y y
                   grind)
                | exact superpose b17e88 b17e1499
                | exact resolve b17e1499 b17e88
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e88 b17e1499
              have b17e1552 : x = (M.op y y) := by
                first
                | (have i₁ := b17e1544
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e1544
                | exact resolve b17e1544 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1544
              have b17e1749 : x ≠ y := by
                first
                | (have i₁ := b17e28
                   have i₂ := b17e1552
                   grind)
                | exact superpose b17e1552 b17e28
                | exact resolve b17e28 b17e1552
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e175075 : y = (M.op y x) ∨ x = (k y y) ∨ x = y := by
                first
                | (have i₁ := b17e93 y y
                   have i₂ := b17e1552
                   grind)
                | exact superpose b17e1552 b17e93
                | (have j0 := b17e93 x y
                   grind)
                | exact resolve b17e93 b17e1552
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e93 b17e1552
              have b17e175420 : x = (k y y) ∨ x = y := by
                first
                | (have r₁ := b17e175075
                   have r₂ := b17e55
                   grind)
                | exact resolve b17e175075 b17e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e55 b17e175075
              have b17e175462 : x = (k y y) := by
                first
                | (have r₁ := b17e175420
                   have r₂ := b17e1749
                   grind)
                | exact resolve b17e175420 b17e1749
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1749 b17e175420
              have b17e175512 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b17e437 y
                   have i₂ := b17e175462
                   grind)
                | exact superpose b17e175462 b17e437
                | (have j0 := b17e437 y
                   grind)
                | exact resolve b17e437 b17e175462
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e437
              have b17e222249 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b17e441 y
                   have i₂ := b17e175462
                   grind)
                | exact superpose b17e175462 b17e441
                | (have j0 := b17e441 y
                   grind)
                | exact resolve b17e441 b17e175462
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e441 b17e175462
              have b17e222329 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b17e222249
                   have i₂ := b17e188
                   grind)
                | exact superpose b17e188 b17e222249
                | exact resolve b17e222249 b17e188
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e222249
              have b17e222333 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b17e222329
                   have i₂ := b17e188
                   grind)
                | exact superpose b17e188 b17e222329
                | exact resolve b17e222329 b17e188
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e188 b17e222329
              have b17e222336 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have r₁ := b17e222333
                   have r₂ := b17e175512
                   grind)
                | exact resolve b17e222333 b17e175512
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e175512 b17e222333
              have b17e222354 : y = (k y (τ (σ y))) := by
                first
                | (have i₁ := b17e323 y
                   have i₂ := b17e222336
                   grind)
                | exact superpose b17e222336 b17e323
                | exact resolve b17e323 b17e222336
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e323 b17e222336
              have b17e222744 : y = (k y y) := by
                first
                | (have i₁ := b17e222354
                   have i₂ := b17e16 y
                   grind)
                | exact superpose b17e16 b17e222354
                | exact resolve b17e222354 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e222354
              have b17e223237 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b17e20 y y
                   have i₂ := b17e222744
                   grind)
                | exact superpose b17e222744 b17e20
                | (have j0 := b17e20 y y
                   grind)
                | exact resolve b17e20 b17e222744
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e222744
              have b17e223248 : y = (M.op y y) := by grind
              clear b17e223237
              have b17e223267 : False := by grind
              exact b17e223267
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b18e21 : y ≠ (M.op x x) := by grind
          have b18e22 : x ≠ (M.op x y) := by grind
          have b18e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b18e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e26 : y = (k y y) := by grind
          have b18e27 : (σ x) = (k (σ x) (σ y)) := by grind
          have b18e28 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e27
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e27
            | exact resolve b18e27 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e27
          have b18e44 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b18e13 X0 (σ x) (σ x)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e47 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 X0) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 (σ x) X0 X1
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e19 X1 X0
               have i₂ := b18e18 (σ X1) (σ X0)
               grind)
            | exact superpose b18e18 b18e19
            | (have j1 := b18e18 (σ X1) (σ X0)
               grind)
            | exact resolve b18e19 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e74 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b18e28
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e28
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e28 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e28
          have b18e86 : (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b18e74
               have r₂ := b18e21
               grind)
            | exact resolve b18e74 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e74
          have b18e89 : (σ x) = (σ (M.op y x)) := by
            first
            | (have r₁ := b18e86
               have r₂ := b18e22
               grind)
            | exact resolve b18e86 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e86
          have b18e114 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b18e44 (M.op (σ y) (σ y))
               have i₂ := b18e13 (σ y) (σ y) (σ y)
               grind)
            | exact superpose b18e13 b18e44
            | exact resolve b18e44 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e44
          have b18e844 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e71 y y
               have i₂ := b18e114
               grind)
            | exact superpose b18e114 b18e71
            | exact resolve b18e71 b18e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e866 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b18e844
          have b18e871 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e866
               have i₂ := b18e26
               grind)
            | exact superpose b18e26 b18e866
            | exact resolve b18e866 b18e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e866
          have b18e872 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b18e871
          have b18e876 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b18e20
               have i₂ := b18e872
               grind)
            | exact superpose b18e872 b18e20
            | exact resolve b18e20 b18e872
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e881 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b18e47 (σ y) (σ x)
               have i₂ := b18e872
               grind)
            | exact superpose b18e872 b18e47
            | exact resolve b18e47 b18e872
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e47
          have b18e884 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b18e881
               have i₂ := b18e114
               grind)
            | exact superpose b18e114 b18e881
            | exact resolve b18e881 b18e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e114 b18e881
          have b18e885 : (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b18e884
               have i₂ := b18e872
               grind)
            | exact superpose b18e872 b18e884
            | exact resolve b18e884 b18e872
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e872 b18e884
          have b18e1045 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e71 y y
               have i₂ := b18e885
               grind)
            | exact superpose b18e885 b18e71
            | exact resolve b18e71 b18e885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e71 b18e885
          have b18e1069 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b18e1045
          have b18e1077 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e1069
               have i₂ := b18e26
               grind)
            | exact superpose b18e26 b18e1069
            | exact resolve b18e1069 b18e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e26 b18e1069
          have b18e1078 : (σ x) = (σ y) := by grind
          clear b18e1077
          have b18e1162 : y = (τ (σ x)) := by
            first
            | (have i₁ := b18e14 y
               have i₂ := b18e1078
               grind)
            | exact superpose b18e1078 b18e14
            | exact resolve b18e14 b18e1078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1078
          have b18e1179 : x = y := by
            first
            | (have i₁ := b18e1162
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e1162
            | exact resolve b18e1162 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1162
          have b18e1285 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b18e89
               have i₂ := b18e1179
               grind)
            | exact superpose b18e1179 b18e89
            | exact resolve b18e89 b18e1179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e89
          have b18e1299 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b18e876
               have i₂ := b18e1179
               grind)
            | exact superpose b18e1179 b18e876
            | exact resolve b18e876 b18e1179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e876 b18e1179
          have b18e1303 : False := by grind
          exact b18e1303
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b19e25 : y ≠ (M.op y y) := by grind
            have b19e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : False := by grind
            exact b19e28
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op x x) := by grind
            have b20e23 : x ≠ (M.op x y) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b20e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ x) = (k (σ x) (σ y)) := by grind
            have b20e29 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b20e28
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e34 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e29
                 grind)
              | exact superpose b20e29 b20e15
              | exact resolve b20e15 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e35 : x = (k x y) := by
              first
              | (have i₁ := b20e34
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e34
              | exact resolve b20e34 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e34
            have b20e63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 X1 X0
                 have i₂ := b20e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b20e19 b20e20
              | (have j1 := b20e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b20e20 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e65 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b20e35
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e35
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e35 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e74 : x = (M.op y x) ∨ x = (M.op x y) := by
              first
              | (have r₁ := b20e65
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e65 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e65
            have b20e77 : x = (M.op y x) := by
              first
              | (have r₁ := b20e74
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e74 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e74
            have b20e501 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e63 x x
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e63
              | exact resolve b20e63 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e63
            have b20e578 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
            clear b20e501
            have b20e887 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e15 (k x x)
                 have i₂ := b20e578
                 grind)
              | exact superpose b20e578 b20e15
              | exact resolve b20e15 b20e578
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e903 : y = (k x x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e887
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e887
              | exact resolve b20e887 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e887
            have b20e911 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e19 x x
                 have i₂ := b20e903
                 grind)
              | exact superpose b20e903 b20e19
              | (have j0 := b20e19 x x
                 grind)
              | exact resolve b20e19 b20e903
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e903
            have b20e912 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
            clear b20e911
            have b20e914 : x = (M.op x x) ∨ (σ x) = (σ y) := by
              first
              | (have r₁ := b20e912
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e912 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e912
            have b20e1004 : x = (k x x) ∨ (σ x) = (σ y) := by grind
            clear b20e914
            have b20e1149 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e578
                 have i₂ := b20e1004
                 grind)
              | exact superpose b20e1004 b20e578
              | exact resolve b20e578 b20e1004
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e578 b20e1004
            have b20e1156 : (σ x) = (σ y) := by grind
            clear b20e1149
            have b20e1280 : x = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 x
                 have i₂ := b20e1156
                 grind)
              | exact superpose b20e1156 b20e15
              | exact resolve b20e15 b20e1156
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1156
            have b20e1295 : x = y := by
              first
              | (have i₁ := b20e1280
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e1280
              | exact resolve b20e1280 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1280
            have b20e1413 : y = (M.op y y) := by
              first
              | (have i₁ := b20e77
                 have i₂ := b20e1295
                 grind)
              | exact superpose b20e1295 b20e77
              | exact resolve b20e77 b20e1295
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e77 b20e1295
            have b20e1421 : False := by grind
            exact b20e1421
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : y ≠ (M.op x x) := by grind
            have b21e23 : x ≠ (M.op x y) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b21e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
            have b21e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e29 : y = (k y y) := by grind
            have b21e32 : ∀ X0 : G, (M.op y (M.op y (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b21e14 X0 y y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
                 have i₂ := b21e14 X0 X2 X1
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e36 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
                 have i₂ := b21e14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e41 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b21e18 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e18
              | (have j0 := b21e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b21e18 (σ x) (σ y)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e18 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b21e41
            have b21e44 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e43
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e43 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e43
            have b21e46 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e44
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e44
              | exact resolve b21e44 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e44
            have b21e49 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e46
                 grind)
              | exact superpose b21e46 b21e15
              | exact resolve b21e15 b21e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e46
            have b21e50 : x = (k x y) := by
              first
              | (have i₁ := b21e49
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e49
              | exact resolve b21e49 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e49
            have b21e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e20 X1 X0
                 have i₂ := b21e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b21e19 b21e20
              | (have j1 := b21e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b21e20 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e71 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e50
                 grind)
              | exact superpose b21e50 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50
            have b21e72 : x = (M.op y x) ∨ x = (M.op x y) := by
              first
              | (have r₁ := b21e71
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e71 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e71
            have b21e74 : x = (M.op y x) := by
              first
              | (have r₁ := b21e72
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e72 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e72
            have b21e137 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b21e14 X0 X0 X0
                 have i₂ := b21e36 X0 X0
                 grind)
              | exact superpose b21e36 b21e14
              | exact resolve b21e14 b21e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e192 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
              intro X0 X3
              first
              | (have i₁ := b21e36 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
                 have i₂ := b21e34 X0 x x X3
                 grind)
              | exact superpose b21e34 b21e36
              | exact resolve b21e36 b21e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e36
            have b21e195 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
              intro X0 X1 X4
              first
              | (have i₁ := b21e14 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
                 have i₂ := b21e34 X1 x x X0
                 grind)
              | exact superpose b21e34 b21e14
              | exact resolve b21e14 b21e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e34
            have b21e561 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b21e56 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e56
            have b21e562 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b21e561 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e561
            have b21e2074 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op X0 (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b21e32 (M.op X0 (M.op X0 X0))
                 have i₂ := b21e195 X0 X0 X0
                 grind)
              | exact superpose b21e195 b21e32
              | exact resolve b21e32 b21e195
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e32 b21e195
            have b21e2149 : (M.op y x) = (M.op x (M.op x x)) := by
              first
              | (have i₁ := b21e2074 x
                 have i₂ := b21e74
                 grind)
              | exact superpose b21e74 b21e2074
              | exact resolve b21e2074 b21e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2074
            have b21e2213 : x = (M.op x (M.op x x)) := by
              first
              | (have i₁ := b21e2149
                 have i₂ := b21e74
                 grind)
              | exact superpose b21e74 b21e2149
              | exact resolve b21e2149 b21e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e74 b21e2149
            have b21e2357 : x = (M.op x x) := by
              first
              | (have i₁ := b21e137 x
                 have i₂ := b21e2213
                 grind)
              | exact superpose b21e2213 b21e137
              | exact resolve b21e137 b21e2213
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e137 b21e2213
            have b21e2429 : x = (k x x) := by grind
            clear b21e2357
            have b21e3243 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b21e562 x
                 have i₂ := b21e2429
                 grind)
              | exact superpose b21e2429 b21e562
              | (have j0 := b21e562 x
                 grind)
              | exact resolve b21e562 b21e2429
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2429
            have b21e3244 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b21e562 y
                 have i₂ := b21e29
                 grind)
              | exact superpose b21e29 b21e562
              | (have j0 := b21e562 y
                 grind)
              | exact resolve b21e562 b21e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e29 b21e562
            have b21e3249 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b21e3244
            have b21e3250 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b21e3243
            have b21e3290 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
              intro X0
              first
              | (have i₁ := b21e192 (σ y) x
                 have i₂ := b21e3249
                 grind)
              | exact superpose b21e3249 b21e192
              | exact resolve b21e192 b21e3249
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e192 b21e3249
            have b21e3343 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b21e24
                 have i₂ := b21e3250
                 grind)
              | exact superpose b21e3250 b21e24
              | exact resolve b21e24 b21e3250
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3250
            have b21e6486 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b21e3290 (σ x)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e3290
              | exact resolve b21e3290 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3290
            have b21e6523 : (σ x) = (σ y) := by
              first
              | (have i₁ := b21e6486
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e6486
              | exact resolve b21e6486 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e6486
            have b21e6524 : False := by grind
            exact b21e6524
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b22e27 : y ≠ (M.op y y) := by grind
              have b22e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : False := by grind
              exact b22e30
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e24 : x ≠ (M.op x y) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b23e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              have b23e28 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
                   have i₂ := b23e15 X0 X2 X1
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e41 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
                   have i₂ := b23e15 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X1 X0
                   have i₂ := b23e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b23e20 b23e21
                | (have j1 := b23e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b23e21 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e121 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b23e40 X4 X2 X3 (M.op X1 X0)
                   have i₂ := b23e41 X1 X0
                   grind)
                | exact superpose b23e41 b23e40
                | exact resolve b23e40 b23e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e137 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
                intro X0 X1 X4
                first
                | (have i₁ := b23e15 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
                   have i₂ := b23e40 X1 x x X0
                   grind)
                | exact superpose b23e40 b23e15
                | exact resolve b23e15 b23e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e40
              have b23e849 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X3)) (M.op X3 (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e137 X3 X2 (M.op X1 X0)
                   have i₂ := b23e41 X1 X0
                   grind)
                | exact superpose b23e41 b23e137
                | exact resolve b23e137 b23e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e41
              have b23e876 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X0 (M.op X0 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e15 (M.op X0 (M.op X0 X0)) X1 X2
                   have i₂ := b23e137 X0 X0 X0
                   grind)
                | exact superpose b23e137 b23e15
                | exact resolve b23e15 b23e137
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e137
              have b23e4395 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b23e121 X0 (M.op X1 X0) X2 X3 X4
                   have i₂ := b23e876 X0 X0 X1
                   grind)
                | exact superpose b23e876 b23e121
                | exact resolve b23e121 b23e876
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e121 b23e876
              have b23e4538 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                first
                | (have i₁ := b23e4395 X0 X1 x x x
                   have i₂ := b23e849 X0 X0 (M.op x x) x
                   grind)
                | exact superpose b23e849 b23e4395
                | exact resolve b23e4395 b23e849
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e849 b23e4395
              have b23e4670 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e4538 (σ y) (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e4538
                | exact resolve b23e4538 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e4766 : (σ x) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e4670
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e4670
                | exact resolve b23e4670 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4670
              have b23e4909 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b23e64 y y
                   have i₂ := b23e4766
                   grind)
                | exact superpose b23e4766 b23e64
                | exact resolve b23e64 b23e4766
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e64 b23e4766
              have b23e4959 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
              clear b23e4909
              have b23e8234 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b23e16 (k y y)
                   have i₂ := b23e4959
                   grind)
                | exact superpose b23e4959 b23e16
                | exact resolve b23e16 b23e4959
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4959
              have b23e8270 : x = (k y y) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b23e8234
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e8234
                | exact resolve b23e8234 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e8234
              have b23e8731 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b23e20 y y
                   have i₂ := b23e8270
                   grind)
                | exact superpose b23e8270 b23e20
                | (have j0 := b23e20 y y
                   grind)
                | exact resolve b23e20 b23e8270
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e8270
              have b23e8735 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
              clear b23e8731
              have b23e8740 : x = (M.op y y) ∨ (σ x) = (σ y) := by
                first
                | (have r₁ := b23e8735
                   have r₂ := b23e28
                   grind)
                | exact resolve b23e8735 b23e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e8735
              have b23e8863 : x = (M.op x y) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b23e4538 y y
                   have i₂ := b23e8740
                   grind)
                | exact superpose b23e8740 b23e4538
                | exact resolve b23e4538 b23e8740
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4538 b23e8740
              have b23e8864 : (σ x) = (σ y) := by
                first
                | (have r₁ := b23e8863
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e8863 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e8863
              have b23e9092 : (σ y) ≠ (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e25
                   have i₂ := b23e8864
                   grind)
                | exact superpose b23e8864 b23e25
                | exact resolve b23e25 b23e8864
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e9093 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e26
                   have i₂ := b23e8864
                   grind)
                | exact superpose b23e8864 b23e26
                | exact resolve b23e26 b23e8864
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e8864
              have b23e9157 : False := by grind
              exact b23e9157
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b24e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e23 : x ≠ (M.op x y) := by grind
            have b24e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b24e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : y = (k y y) := by grind
            have b24e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 (τ X0) X1
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e31 : ∀ X0 : G, (M.op y (M.op y (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b24e14 X0 y y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
                 have i₂ := b24e14 X0 X2 X1
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e33 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) y)) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 y X0 X1
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
                 have i₂ := b24e14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e36 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 (M.op y (M.op X0 X0)) y
                 have i₂ := b24e31 X0
                 grind)
              | exact superpose b24e31 b24e14
              | exact resolve b24e14 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e42 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 X0)) (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b24e33 (M.op y (M.op X0 X0)) y
                 have i₂ := b24e31 X0
                 grind)
              | exact superpose b24e31 b24e33
              | exact resolve b24e33 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e55 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X3 ∨ (k X3 X0) = (M.op X0 X3) ∨ (M.op X3 X0) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X3 X1 X2
                 have i₂ := b24e19 X3 X0
                 grind)
              | (have i₁ := b24e14 X0 X1 X2
                 have i₂ := b24e19 X0 (M.op X0 X0)
                 grind)
              | exact superpose b24e19 b24e14
              | (have j1 := b24e19 X3 X0
                 grind)
              | exact resolve b24e14 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 X1 X1
                 have i₂ := b24e19 (M.op X1 X1) X0
                 grind)
              | (have i₁ := b24e14 X0 X1 x
                 have i₂ := b24e19 X0 (M.op (M.op x X1) (M.op X0 X0))
                 grind)
              | exact superpose b24e19 b24e14
              | (have j1 := b24e19 (M.op X1 X1) X0
                 grind)
              | exact resolve b24e14 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b24e24
                 have i₂ := b24e19 (σ x) X0
                 grind)
              | (have i₁ := b24e24
                 have i₂ := b24e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b24e19 b24e24
              | (have j1 := b24e19 (σ x) X0
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e19 (σ x) (σ y)
                 grind)
              | exact resolve b24e24 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e118 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e34 X0 X0
                 have i₂ := b24e19 X0 X1
                 grind)
              | (have i₁ := b24e34 X0 X1
                 have i₂ := b24e19 X0 (M.op X0 X1)
                 grind)
              | exact superpose b24e19 b24e34
              | (have j1 := b24e19 X1 X0
                 grind)
              | exact resolve b24e34 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e121 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b24e14 X0 X0 X0
                 have i₂ := b24e34 X0 X0
                 grind)
              | exact superpose b24e34 b24e14
              | exact resolve b24e14 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e123 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op y (M.op X0 (M.op X1 X0)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e31 (M.op X1 X0)
                 have i₂ := b24e34 X1 X0
                 grind)
              | exact superpose b24e34 b24e31
              | exact resolve b24e31 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e124 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 (M.op X1 X0) X2 X3
                 have i₂ := b24e34 X1 X0
                 grind)
              | exact superpose b24e34 b24e14
              | exact resolve b24e14 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e125 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
              intro X0 X1
              grind
            have b24e138 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 (M.op X0 (M.op X0 X0)) X0
                 have i₂ := b24e121 X0
                 grind)
              | exact superpose b24e121 b24e14
              | exact resolve b24e14 b24e121
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e121
            have b24e153 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 (M.op X1 X0))) (M.op (M.op X1 X0) (M.op X4 X4))) = X4 := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e32 (M.op X1 X0) X2 X3 X4
                 have i₂ := b24e34 X1 X0
                 grind)
              | exact superpose b24e34 b24e32
              | exact resolve b24e32 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e161 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e32 X4 X2 X3 (M.op X1 X0)
                 have i₂ := b24e34 X1 X0
                 grind)
              | exact superpose b24e34 b24e32
              | exact resolve b24e32 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e162 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e32 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
                 have i₂ := b24e32 (M.op X0 X1) X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b24e32 b24e32
              | exact resolve b24e32 b24e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e171 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
                 have i₂ := b24e32 (M.op X0 X1) X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b24e32 b24e14
              | exact resolve b24e14 b24e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e174 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op y (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e31 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
                 have i₂ := b24e32 (M.op X0 X1) X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b24e32 b24e31
              | exact resolve b24e31 b24e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e176 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
              intro X0 X3
              first
              | (have i₁ := b24e34 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
                 have i₂ := b24e32 X0 x x X3
                 grind)
              | exact superpose b24e32 b24e34
              | exact resolve b24e34 b24e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e180 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
              intro X0 X1 X4
              first
              | (have i₁ := b24e14 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
                 have i₂ := b24e32 X1 x x X0
                 grind)
              | exact superpose b24e32 b24e14
              | exact resolve b24e14 b24e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32
            have b24e183 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op y (M.op y (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e174 X0 X1
                 have i₂ := b24e34 X0 X1
                 grind)
              | exact superpose b24e34 b24e174
              | exact resolve b24e174 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e174
            have b24e186 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e171 X0 X1 X2 X3
                 have i₂ := b24e34 X0 X1
                 grind)
              | exact superpose b24e34 b24e171
              | exact resolve b24e171 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e171
            have b24e191 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e162 X0 X1 X2 X3 X4
                 have i₂ := b24e34 X0 X1
                 grind)
              | exact superpose b24e34 b24e162
              | exact resolve b24e162 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e162
            have b24e196 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op y (M.op X0 X1))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e186 X0 X1 X2 X3
                 have i₂ := b24e183 X0 X1
                 grind)
              | exact superpose b24e183 b24e186
              | exact resolve b24e186 b24e183
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e186
            have b24e201 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op y (M.op X0 X1))) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e191 X0 X1 X2 X3 X4
                 have i₂ := b24e183 X0 X1
                 grind)
              | exact superpose b24e183 b24e191
              | exact resolve b24e191 b24e183
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e183 b24e191
            have b24e258 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b24e61 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e61
            have b24e259 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have r₁ := b24e258
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e258 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e258
            have b24e260 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e259
                 have i₂ := b24e20 x y
                 grind)
              | exact superpose b24e20 b24e259
              | exact resolve b24e259 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e259
            have b24e269 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) y) (M.op y X2)) = X3 ∨ (M.op X2 X3) = (k X3 X2) ∨ (M.op X3 X2) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e55 X2 (M.op (M.op X0 X1) y) X1 X3
                 have i₂ := b24e33 X1 X0
                 grind)
              | exact superpose b24e33 b24e55
              | (have j0 := b24e55 X2 X1 X2 X3
                 grind)
              | exact resolve b24e55 b24e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33 b24e55
            have b24e418 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op y (M.op X1 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 (M.op X0 y) (M.op y (M.op X0 X0))
                 have i₂ := b24e42 X0
                 grind)
              | exact superpose b24e42 b24e14
              | exact resolve b24e14 b24e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e42
            have b24e443 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op y X0) ∨ y = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b24e60 X0 y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e60
              | (have j0 := b24e60 X0 y
                 grind)
              | exact resolve b24e60 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e452 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op y X0) := by
              intro X0
              first
              | (have j0 := b24e443 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e443
            have b24e587 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e18 (σ X1) (σ X0)
                 have i₂ := b24e53 X0 X1
                 grind)
              | exact superpose b24e53 b24e18
              | (have j0 := b24e18 (σ X0) (σ X1)
                 have j1 := b24e53 X1 X0
                 grind)
              | (have r₁ := b24e18 (σ X0) (σ X0)
                 have r₂ := b24e53 X0 X0
                 grind)
              | (have r₁ := b24e18 (σ X1) (σ X0)
                 have r₂ := b24e53 X0 X1
                 grind)
              | exact resolve b24e18 b24e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e594 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e53 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e53
            have b24e595 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e594 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e594
            have b24e597 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have j0 := b24e587 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e587
            have b24e598 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have j0 := b24e597 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e597
            have b24e617 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e598 X0 X1
                 have i₂ := b24e20 X0 X1
                 grind)
              | exact superpose b24e20 b24e598
              | (have j0 := b24e598 X0 X1
                 grind)
              | exact resolve b24e598 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e598
            have b24e796 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ y = (M.op y (τ X0)) := by
              intro X0
              first
              | (have i₁ := b24e30 X0 y
                 have i₂ := b24e452 (τ X0)
                 grind)
              | exact superpose b24e452 b24e30
              | (have j1 := b24e452 (τ X0)
                 grind)
              | exact resolve b24e30 b24e452
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e30 b24e452
            have b24e1410 : (σ (k x y)) = (M.op y (M.op y (M.op (σ x) (σ (k x y))))) := by
              first
              | (have i₁ := b24e123 (σ x) (σ y)
                 have i₂ := b24e260
                 grind)
              | exact superpose b24e260 b24e123
              | exact resolve b24e123 b24e260
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1418 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e123 (M.op X0 X0) (M.op X1 (M.op X0 X0))
                 have i₂ := b24e14 X0 (M.op X0 X0) X1
                 grind)
              | exact superpose b24e14 b24e123
              | exact resolve b24e123 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1536 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (k (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e125 (M.op X0 X0) (M.op X1 (M.op X0 X0))
                 have i₂ := b24e14 X0 (M.op X0 X0) X1
                 grind)
              | exact superpose b24e14 b24e125
              | exact resolve b24e125 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e125
            have b24e1556 : ∀ X0 : G, (M.op y (M.op y X0)) = (k (M.op y (M.op y X0)) X0) := by
              intro X0
              first
              | (have i₁ := b24e1536 X0 x
                 have i₂ := b24e1418 X0 x
                 grind)
              | exact superpose b24e1418 b24e1536
              | exact resolve b24e1536 b24e1418
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1536
            have b24e1662 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e180 X2 X1 (M.op X0 (M.op X0 X0))
                 have i₂ := b24e180 X0 X0 X0
                 grind)
              | exact superpose b24e180 b24e180
              | exact resolve b24e180 b24e180
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1702 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op X0 (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b24e31 (M.op X0 (M.op X0 X0))
                 have i₂ := b24e180 X0 X0 X0
                 grind)
              | exact superpose b24e180 b24e31
              | exact resolve b24e31 b24e180
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1706 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op y (M.op X1 X1)) (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e36 X1 (M.op X0 (M.op X0 X0))
                 have i₂ := b24e180 X0 X0 X0
                 grind)
              | exact superpose b24e180 b24e36
              | exact resolve b24e36 b24e180
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1717 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e176 (M.op x (M.op x x)) x
                 have i₂ := b24e180 x x x
                 grind)
              | exact superpose b24e180 b24e176
              | exact resolve b24e176 b24e180
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1794 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y (M.op y (M.op y X0)))) := by
              intro X0
              first
              | (have i₁ := b24e123 X0 X0
                 have i₂ := b24e1702 X0
                 grind)
              | (have i₁ := b24e123 y y
                 have i₂ := b24e1702 y
                 grind)
              | exact superpose b24e1702 b24e123
              | exact resolve b24e123 b24e1702
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e2141 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op X0 (M.op (M.op y (M.op X0 X0)) (M.op (M.op y (M.op X0 X0)) (M.op y (M.op X0 X0))))) := by
              intro X0
              first
              | (have i₁ := b24e1717 (M.op y (M.op X0 X0)) y
                 have i₂ := b24e31 X0
                 grind)
              | exact superpose b24e31 b24e1717
              | exact resolve b24e1717 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e2153 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op y X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e1717 X0 X1
                 have i₂ := b24e1702 X0
                 grind)
              | (have i₁ := b24e1717 y X1
                 have i₂ := b24e1702 y
                 grind)
              | exact superpose b24e1702 b24e1717
              | exact resolve b24e1717 b24e1702
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e2182 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op X0 (M.op y (M.op y (M.op y (M.op X0 X0))))) := by
              intro X0
              first
              | (have i₁ := b24e2141 X0
                 have i₂ := b24e1702 (M.op y (M.op X0 X0))
                 grind)
              | exact superpose b24e1702 b24e2141
              | exact resolve b24e2141 b24e1702
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1702 b24e2141
            have b24e2202 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
              intro X0
              first
              | (have i₁ := b24e2182 X0
                 have i₂ := b24e31 X0
                 grind)
              | exact superpose b24e31 b24e2182
              | exact resolve b24e2182 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2182
            have b24e2404 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e124 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X2 X3
                 have i₂ := b24e14 X0 (M.op X0 X0) X1
                 grind)
              | exact superpose b24e14 b24e124
              | exact resolve b24e124 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e124
            have b24e2474 : ∀ X0 X2 X3 : G, (M.op y (M.op y X0)) = (M.op X2 (M.op (M.op X3 X2) X0)) := by
              intro X0 X2 X3
              first
              | (have i₁ := b24e2404 X0 x X2 X3
                 have i₂ := b24e1418 X0 x
                 grind)
              | exact superpose b24e1418 b24e2404
              | exact resolve b24e2404 b24e1418
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1418 b24e2404
            have b24e2806 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b24e595 y
                 have i₂ := b24e28
                 grind)
              | exact superpose b24e28 b24e595
              | (have j0 := b24e595 y
                 grind)
              | exact resolve b24e595 b24e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28 b24e595
            have b24e2811 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b24e2806
            have b24e2839 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b24e60 X0 (σ y)
                 have i₂ := b24e2811
                 grind)
              | exact superpose b24e2811 b24e60
              | (have j0 := b24e60 X0 (σ y)
                 grind)
              | exact resolve b24e60 b24e2811
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e60
            have b24e2853 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b24e14 X0 (σ y) (σ y)
                 have i₂ := b24e2811
                 grind)
              | exact superpose b24e2811 b24e14
              | exact resolve b24e14 b24e2811
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e2866 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have j0 := b24e2839 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2839
            have b24e3308 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op y (M.op y (M.op X1 (M.op X0 X0)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e196 X1 (M.op X0 X0) (M.op X1 X1) y
                 have i₂ := b24e36 X1 X0
                 grind)
              | exact superpose b24e36 b24e196
              | exact resolve b24e196 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36
            have b24e3321 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op y (M.op y (M.op X0 X1)))) = (M.op y (M.op y (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e196 (M.op X4 (M.op X3 X2)) (M.op X0 X1) X2 X3
                 have i₂ := b24e196 X0 X1 (M.op X3 X2) X4
                 grind)
              | exact superpose b24e196 b24e196
              | exact resolve b24e196 b24e196
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e3368 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op y (M.op X0 (M.op X1 X2))))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 (M.op X0 (M.op X1 X2)) X2 X1
                 have i₂ := b24e196 X0 (M.op X1 X2) (M.op X1 X2) X0
                 grind)
              | exact superpose b24e196 b24e14
              | exact resolve b24e14 b24e196
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e3663 : ∀ X0 : G, (M.op y (M.op X0 (M.op y X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b24e31 X0
                 have i₂ := b24e2202 X0
                 grind)
              | (have i₁ := b24e31 y
                 have i₂ := b24e2202 y
                 grind)
              | exact superpose b24e2202 b24e31
              | exact resolve b24e31 b24e2202
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e3668 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op X0 (M.op y X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e418 X1 X0
                 have i₂ := b24e2202 X0
                 grind)
              | (have i₁ := b24e418 X0 y
                 have i₂ := b24e2202 y
                 grind)
              | exact superpose b24e2202 b24e418
              | exact resolve b24e418 b24e2202
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e418
            have b24e3676 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op y X0)) X0) := by
              intro X0
              first
              | (have i₁ := b24e176 X0 y
                 have i₂ := b24e2202 X0
                 grind)
              | (have i₁ := b24e176 y y
                 have i₂ := b24e2202 y
                 grind)
              | exact superpose b24e2202 b24e176
              | exact resolve b24e176 b24e2202
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e176 b24e2202
            have b24e4480 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have j0 := b24e118 X1 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e118
            have b24e4962 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 y) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e3668 (M.op y X0) X1
                 have i₂ := b24e2153 X0 y
                 grind)
              | exact superpose b24e2153 b24e3668
              | exact resolve b24e3668 b24e2153
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2153 b24e3668
            have b24e5284 : ∀ X0 X1 X2 : G, (M.op y (M.op y (M.op X2 (M.op X1 (M.op X0 X1))))) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e196 X2 (M.op X1 (M.op X0 X1)) (M.op X2 X2) (M.op x x)
                 have i₂ := b24e161 X1 X0 x x X2
                 grind)
              | exact superpose b24e161 b24e196
              | exact resolve b24e196 b24e161
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e5885 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op (M.op X0 X0) (M.op y (M.op X0 X0))) (M.op (M.op X0 X0) (M.op y (M.op X0 X0))))) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e180 (M.op (M.op X0 X0) (M.op y (M.op X0 X0))) X1 X0
                 have i₂ := b24e3676 (M.op X0 X0)
                 grind)
              | exact superpose b24e3676 b24e180
              | exact resolve b24e180 b24e3676
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e180 b24e3676
            have b24e5917 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op (M.op X0 X0) (M.op y (M.op X0 X0))) (M.op (M.op X0 X0) (M.op y (M.op X0 X0))))) (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e5885 X0 X1
                 have i₂ := b24e34 X0 X0
                 grind)
              | exact superpose b24e34 b24e5885
              | exact resolve b24e5885 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5885
            have b24e5949 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y (M.op y (M.op y (M.op y (M.op (M.op X0 X0) (M.op y (M.op X0 X0)))))))) (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e5917 X0 X1
                 have i₂ := b24e1794 (M.op (M.op X0 X0) (M.op y (M.op X0 X0)))
                 grind)
              | exact superpose b24e1794 b24e5917
              | exact resolve b24e5917 b24e1794
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5917
            have b24e5964 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y (M.op (M.op y y) (M.op y (M.op X0 X0))))) (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e5949 X0 X1
                 have i₂ := b24e5284 y (M.op X0 X0) y
                 grind)
              | exact superpose b24e5284 b24e5949
              | exact resolve b24e5949 b24e5284
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5284 b24e5949
            have b24e5973 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y (M.op y (M.op y (M.op X0 X0))))) (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e5964 X0 X1
                 have i₂ := b24e196 y (M.op X0 X0) y y
                 grind)
              | exact superpose b24e196 b24e5964
              | exact resolve b24e5964 b24e196
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5964
            have b24e5981 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op y y) X0)) (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e5973 X0 X1
                 have i₂ := b24e3308 X0 y
                 grind)
              | exact superpose b24e3308 b24e5973
              | exact resolve b24e5973 b24e3308
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5973
            have b24e5988 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y X0)) (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e5981 X0 X1
                 have i₂ := b24e4962 X0 y
                 grind)
              | exact superpose b24e4962 b24e5981
              | exact resolve b24e5981 b24e4962
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4962 b24e5981
            have b24e6511 : ∀ X0 X1 X2 : G, (M.op y (M.op y (M.op (σ y) (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (σ y) (σ y))) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e201 (σ y) (M.op X0 X0) X1 X2 (σ y)
                 have i₂ := b24e2853 X0
                 grind)
              | exact superpose b24e2853 b24e201
              | exact resolve b24e201 b24e2853
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e201 b24e2853
            have b24e6693 : ∀ X0 X1 X2 : G, (M.op y (M.op y (M.op (σ y) (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (σ y)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e6511 X0 X1 X2
                 have i₂ := b24e2811
                 grind)
              | exact superpose b24e2811 b24e6511
              | exact resolve b24e6511 b24e2811
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e6511
            have b24e6762 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (M.op (M.op X1 X2) (σ y)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e6693 X0 X1 X2
                 have i₂ := b24e3308 X0 (σ y)
                 grind)
              | exact superpose b24e3308 b24e6693
              | exact resolve b24e6693 b24e3308
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3308 b24e6693
            have b24e6791 : ∀ X0 X1 X2 : G, (M.op (σ y) X0) = (M.op (M.op (M.op X1 X2) (σ y)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e6762 X0 X1 X2
                 have i₂ := b24e2811
                 grind)
              | exact superpose b24e2811 b24e6762
              | exact resolve b24e6762 b24e2811
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e6762
            have b24e7434 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e161 X1 X1 X2 x (M.op X1 (M.op X1 X1))
                 have i₂ := b24e138 X1 X1
                 grind)
              | exact superpose b24e138 b24e161
              | exact resolve b24e161 b24e138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e138 b24e161
            have b24e7729 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e7434 X1 y (M.op X0 (M.op y X0))
                 have i₂ := b24e3663 X0
                 grind)
              | exact superpose b24e3663 b24e7434
              | exact resolve b24e7434 b24e3663
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e8254 : (M.op (σ x) (σ x)) = (M.op (σ (k x y)) (σ x)) := by
              first
              | (have i₁ := b24e7729 (σ y) (σ x)
                 have i₂ := b24e260
                 grind)
              | exact superpose b24e260 b24e7729
              | exact resolve b24e7729 b24e260
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e9705 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) y) y) = X2 ∨ (M.op y X2) = (k X2 y) ∨ (M.op X2 y) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e269 X0 X1 y X2
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e269
              | (have j0 := b24e269 X0 X1 y X2
                 grind)
              | exact resolve b24e269 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e269
            have b24e9933 : ∀ X2 : G, (M.op y y) = X2 ∨ (M.op y X2) = (k X2 y) ∨ (M.op X2 y) = X2 := by
              intro X2
              first
              | (have i₁ := b24e9705 x x X2
                 have i₂ := b24e7729 (M.op x x) y
                 grind)
              | exact superpose b24e7729 b24e9705
              | (have j0 := b24e9705 x x X2
                 grind)
              | exact resolve b24e9705 b24e7729
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e9705
            have b24e9942 : ∀ X2 : G, (M.op y X2) = (k X2 y) ∨ (M.op X2 y) = X2 := by
              intro X2
              first
              | (have j0 := b24e9933 X2
                 have j1 := b24e4480 X2 y
                 grind)
              | (have r₁ := b24e9933 x
                 have r₂ := b24e4480 x y
                 grind)
              | (have r₁ := b24e9933 (M.op x x)
                 have r₂ := b24e4480 (M.op y y) x
                 grind)
              | (have r₁ := b24e9933 y
                 have r₂ := b24e4480 (k y y) y
                 grind)
              | exact resolve b24e9933 b24e4480
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4480 b24e9933
            have b24e13455 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
              intro X0
              first
              | (have i₁ := b24e2474 X0 (σ y) (σ y)
                 have i₂ := b24e2811
                 grind)
              | exact superpose b24e2811 b24e2474
              | exact resolve b24e2474 b24e2811
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2811
            have b24e13618 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = (M.op (M.op y (M.op y X0)) (M.op (M.op X1 X2) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e7729 X2 (M.op (M.op X1 X2) X0)
                 have i₂ := b24e2474 X0 X2 X1
                 grind)
              | exact superpose b24e2474 b24e7729
              | exact resolve b24e7729 b24e2474
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e7729
            have b24e13631 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y (M.op y X0))) = (M.op y (M.op y (M.op (M.op X3 (M.op X2 X1)) X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e196 (M.op X3 (M.op X2 X1)) X0 X1 X2
                 have i₂ := b24e2474 X0 (M.op X2 X1) X3
                 grind)
              | exact superpose b24e2474 b24e196
              | exact resolve b24e196 b24e2474
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e196
            have b24e13634 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op (M.op y (M.op y X0)) (M.op (M.op X1 (M.op X2 X3)) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e7434 (M.op (M.op X1 (M.op X2 X3)) X0) X2 X3
                 have i₂ := b24e2474 X0 (M.op X2 X3) X1
                 grind)
              | exact superpose b24e2474 b24e7434
              | exact resolve b24e7434 b24e2474
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2474 b24e7434
            have b24e13686 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op y (M.op y (M.op y (M.op (M.op X1 (M.op X2 X3)) X0))))) = (M.op (M.op y (M.op y X0)) (M.op (M.op X1 (M.op X2 X3)) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e13634 X0 X1 X2 X3
                 have i₂ := b24e1794 (M.op (M.op X1 (M.op X2 X3)) X0)
                 grind)
              | exact superpose b24e1794 b24e13634
              | exact resolve b24e13634 b24e1794
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1794 b24e13634
            have b24e13690 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X0)) = (M.op (M.op y (M.op y X0)) (M.op (M.op X1 X2) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e13618 X0 X1 X2
                 have i₂ := b24e34 (M.op X1 X2) X0
                 grind)
              | exact superpose b24e34 b24e13618
              | exact resolve b24e13618 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e13618
            have b24e13743 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y (M.op y X0)) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op y (M.op y (M.op X3 (M.op y (M.op y X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e13686 X0 X1 X2 X3
                 have i₂ := b24e13631 X0 X3 X2 X1
                 grind)
              | exact superpose b24e13631 b24e13686
              | exact resolve b24e13686 b24e13631
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e13631 b24e13686
            have b24e13756 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y X0))))) = (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e13743 X0 X1 X2 X3
                 have i₂ := b24e13690 X0 X1 (M.op X2 X3)
                 grind)
              | exact superpose b24e13690 b24e13743
              | exact resolve b24e13743 b24e13690
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e13690 b24e13743
            have b24e21919 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
              intro X0 X1
              grind
            clear b24e617
            have b24e22051 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e21919 X0 X1
                 have i₂ := b24e20 X1 X0
                 grind)
              | exact superpose b24e20 b24e21919
              | (have j0 := b24e21919 X0 X1
                 grind)
              | exact resolve b24e21919 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e21919
            have b24e22052 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have j0 := b24e22051 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e22051
            have b24e55351 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (σ y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e6791 X1 y (M.op y (M.op X0 X0))
                 have i₂ := b24e31 X0
                 grind)
              | exact superpose b24e31 b24e6791
              | exact resolve b24e6791 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31 b24e6791
            have b24e98740 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0))))) := by
              intro X0 X1
              first
              | (have i₁ := b24e5988 (M.op X0 (M.op y X0)) X1
                 have i₂ := b24e3663 X0
                 grind)
              | exact superpose b24e3663 b24e5988
              | exact resolve b24e5988 b24e3663
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3663 b24e5988
            have b24e99430 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X1 X0) (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op X0 (M.op y X0)))))))) := by
              intro X0 X1
              first
              | (have i₁ := b24e98740 X0 X1
                 have i₂ := b24e13756 (M.op X0 (M.op y X0)) X0 y X0
                 grind)
              | exact superpose b24e13756 b24e98740
              | exact resolve b24e98740 b24e13756
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e13756 b24e98740
            have b24e99502 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X1 X0) (M.op y (M.op y (M.op X0 (M.op y X0))))) := by
              intro X0 X1
              first
              | (have i₁ := b24e99430 X0 X1
                 have i₂ := b24e3368 X0 y X0
                 grind)
              | exact superpose b24e3368 b24e99430
              | exact resolve b24e99430 b24e3368
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3368 b24e99430
            have b24e99538 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X1 X0) (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e99502 X0 X1
                 have i₂ := b24e123 X0 y
                 grind)
              | exact superpose b24e123 b24e99502
              | exact resolve b24e99502 b24e123
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e99502
            have b24e121029 : (M.op (σ x) (σ x)) = (M.op (σ (M.op y x)) (σ x)) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b24e8254
                 have i₂ := b24e9942 x
                 grind)
              | exact superpose b24e9942 b24e8254
              | (have j1 := b24e9942 x
                 grind)
              | exact resolve b24e8254 b24e9942
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e8254
            have b24e121156 : (M.op (σ x) (σ x)) = (M.op (σ (M.op y x)) (σ x)) := by
              first
              | (have r₁ := b24e121029
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e121029 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e121029
            have b24e143632 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op y (M.op y (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2)))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e123 X2 X2
                 have i₂ := b24e1662 X2 X0 X1
                 grind)
              | exact superpose b24e1662 b24e123
              | exact resolve b24e123 b24e1662
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e144293 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op y (M.op y (M.op X1 X2)))) := by
              intro X1 X2
              first
              | (have i₁ := b24e143632 x X1 X2
                 have i₂ := b24e3321 X1 X2 X1 X1 x
                 grind)
              | exact superpose b24e3321 b24e143632
              | exact resolve b24e143632 b24e3321
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3321 b24e143632
            have b24e148788 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op X1 X1)) (M.op y (M.op y (M.op X0 (M.op X0 X0))))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e144293 (M.op X2 (M.op X1 X1)) (M.op X1 X0)
                 have i₂ := b24e1662 X0 X2 X1
                 grind)
              | exact superpose b24e1662 b24e144293
              | exact resolve b24e144293 b24e1662
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1662 b24e144293
            have b24e149889 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e148788 X0 X1 X2
                 have i₂ := b24e123 X0 X0
                 grind)
              | exact superpose b24e123 b24e148788
              | exact resolve b24e148788 b24e123
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e123 b24e148788
            have b24e150163 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X1 X1)) (M.op X0 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e149889 X0 X1 X2
                 have i₂ := b24e34 X1 X0
                 grind)
              | exact superpose b24e34 b24e149889
              | exact resolve b24e149889 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e34 b24e149889
            have b24e151029 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 (M.op X0 X0)) (M.op X4 X4))) = X4 := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e153 (M.op X1 X0) (M.op y (M.op X1 X1)) X2 X3 X4
                 have i₂ := b24e1706 X0 X1
                 grind)
              | exact superpose b24e1706 b24e153
              | exact resolve b24e153 b24e1706
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e153 b24e1706
            have b24e151127 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op X0 (M.op X0 X0)))) (M.op X4 (M.op X0 X4))) = X4 := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e151029 X0 X1 X2 X3 X4
                 have i₂ := b24e150163 X4 X0 X0
                 grind)
              | exact superpose b24e150163 b24e151029
              | exact resolve b24e151029 b24e150163
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e150163 b24e151029
            have b24e151580 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X4 (M.op X0 X4))) = X4 := by
              intro X0 X1 X2 X4
              first
              | (have i₁ := b24e151127 X0 X1 X2 x X4
                 have i₂ := b24e1717 X0 x
                 grind)
              | exact superpose b24e1717 b24e151127
              | exact resolve b24e151127 b24e1717
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1717 b24e151127
            have b24e154269 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op (σ x) (σ (k x y)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e151580 (σ y) X0 X1 (σ x)
                 have i₂ := b24e260
                 grind)
              | exact superpose b24e260 b24e151580
              | exact resolve b24e151580 b24e260
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e151580
            have b24e154602 : (σ x) = (M.op (σ y) (M.op (σ x) (σ (k x y)))) := by
              first
              | (have i₁ := b24e154269 x x
                 have i₂ := b24e55351 (M.op x x) (M.op (σ x) (σ (k x y)))
                 grind)
              | exact superpose b24e55351 b24e154269
              | exact resolve b24e154269 b24e55351
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e55351 b24e154269
            have b24e160698 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ y = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b24e796 (σ X0)
                 have i₂ := b24e15 X0
                 grind)
              | exact superpose b24e15 b24e796
              | exact resolve b24e796 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e796
            have b24e160732 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b24e160698 X0
                 have i₂ := b24e20 y X0
                 grind)
              | exact superpose b24e20 b24e160698
              | (have j0 := b24e160698 X0
                 grind)
              | exact resolve b24e160698 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e160698
            have b24e161512 : (σ (M.op y x)) = (M.op y (M.op y (M.op (σ x) (σ (M.op y x))))) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b24e1410
                 have i₂ := b24e9942 x
                 grind)
              | exact superpose b24e9942 b24e1410
              | (have j1 := b24e9942 x
                 grind)
              | exact resolve b24e1410 b24e9942
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1410
            have b24e161679 : (σ (M.op y x)) = (M.op y (M.op y (M.op (σ x) (σ (M.op y x))))) := by
              first
              | (have r₁ := b24e161512
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e161512 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e161512
            have b24e185953 : (σ x) = (M.op (σ y) (M.op (σ x) (σ (M.op y x)))) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b24e154602
                 have i₂ := b24e9942 x
                 grind)
              | exact superpose b24e9942 b24e154602
              | (have j1 := b24e9942 x
                 grind)
              | exact resolve b24e154602 b24e9942
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e9942 b24e154602
            have b24e186115 : (σ x) = (M.op (σ y) (M.op (σ x) (σ (M.op y x)))) := by
              first
              | (have r₁ := b24e185953
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e185953 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e185953
            have b24e212855 : (M.op (σ y) (σ x)) = (M.op y (M.op y (M.op (σ x) (σ (M.op y x))))) := by
              first
              | (have i₁ := b24e13455 (M.op (σ x) (σ (M.op y x)))
                 have i₂ := b24e186115
                 grind)
              | exact superpose b24e186115 b24e13455
              | exact resolve b24e13455 b24e186115
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e13455 b24e186115
            have b24e213021 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
              first
              | (have i₁ := b24e212855
                 have i₂ := b24e161679
                 grind)
              | exact superpose b24e161679 b24e212855
              | exact resolve b24e212855 b24e161679
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e161679 b24e212855
            have b24e213090 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e22052 X0 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e22052
              | exact resolve b24e22052 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e213112 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e22052 x y
                 grind)
              | exact superpose b24e22052 b24e21
              | (have j1 := b24e22052 x y
                 grind)
              | exact resolve b24e21 b24e22052
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e22052
            have b24e213445 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e213090 X0 X1
                 have i₂ := b24e29 X0 X1
                 grind)
              | exact superpose b24e29 b24e213090
              | (have j0 := b24e213090 X0 X1
                 grind)
              | exact resolve b24e213090 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e213090
            have b24e213464 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e213445 X0 X1
                 have i₂ := b24e29 X0 X1
                 grind)
              | exact superpose b24e29 b24e213445
              | (have j0 := b24e213445 X0 X1
                 grind)
              | exact resolve b24e213445 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e29 b24e213445
            have b24e213479 : (σ (k x y)) = (σ (M.op y x)) := by
              first
              | (have i₁ := b24e260
                 have i₂ := b24e213021
                 grind)
              | exact superpose b24e213021 b24e260
              | exact resolve b24e260 b24e213021
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e327639 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e213464 X0 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e213464
              | exact resolve b24e213464 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e213464
            have b24e328385 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              first
              | (have j0 := b24e327639 X1 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e327639
            have b24e726933 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b24e20 y X0
                 have i₂ := b24e2866 (σ X0)
                 grind)
              | exact superpose b24e2866 b24e20
              | (have j1 := b24e2866 (σ X0)
                 grind)
              | exact resolve b24e20 b24e2866
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2866
            have b24e729282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b24e213112
                 have i₂ := b24e160732 x
                 grind)
              | exact superpose b24e160732 b24e213112
              | (have j1 := b24e160732 x
                 grind)
              | (have r₁ := b24e213112
                 have r₂ := b24e160732 x
                 grind)
              | exact resolve b24e213112 b24e160732
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e160732 b24e213112
            have b24e729283 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
            clear b24e729282
            have b24e729315 : (M.op x y) = (τ (σ y)) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b24e15 (M.op x y)
                 have i₂ := b24e729283
                 grind)
              | exact superpose b24e729283 b24e15
              | exact resolve b24e15 b24e729283
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e729283
            have b24e729355 : y = (M.op y x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b24e729315
                 have i₂ := b24e15 y
                 grind)
              | exact superpose b24e15 b24e729315
              | exact resolve b24e729315 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e729315
            have b24e729479 : (M.op y y) = (k (M.op y y) x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b24e1556 x
                 have i₂ := b24e729355
                 grind)
              | exact superpose b24e729355 b24e1556
              | exact resolve b24e1556 b24e729355
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1556
            have b24e729753 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b24e99538 x y
                 have i₂ := b24e729355
                 grind)
              | exact superpose b24e729355 b24e99538
              | exact resolve b24e99538 b24e729355
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e99538 b24e729355
            have b24e729963 : y = (M.op x y) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b24e729753
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e729753
              | exact resolve b24e729753 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e729753
            have b24e729964 : y = (M.op x y) := by grind
            clear b24e729963
            have b24e730135 : y = (k y x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b24e729479
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e729479
              | exact resolve b24e729479 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e729479
            have b24e730179 : y = (k y x) := by
              first
              | (have j1 := b24e328385 y x
                 grind)
              | (have r₁ := b24e730135
                 have r₂ := b24e328385 y x
                 grind)
              | exact resolve b24e730135 b24e328385
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e328385 b24e730135
            have b24e1457186 : (σ y) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
              first
              | (have i₁ := b24e213021
                 have i₂ := b24e726933 x
                 grind)
              | exact superpose b24e726933 b24e213021
              | (have j1 := b24e726933 x
                 grind)
              | exact resolve b24e213021 b24e726933
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e213021 b24e726933
            have b24e1457221 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y x)) := by
              first
              | (have i₁ := b24e1457186
                 have i₂ := b24e730179
                 grind)
              | exact superpose b24e730179 b24e1457186
              | exact resolve b24e1457186 b24e730179
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e730179 b24e1457186
            have b24e1457244 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op y x)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e1457221
                 grind)
              | exact superpose b24e1457221 b24e21
              | exact resolve b24e21 b24e1457221
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1457221
            have b24e1457426 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y x)) := by
              first
              | (have i₁ := b24e1457244
                 have i₂ := b24e729964
                 grind)
              | exact superpose b24e729964 b24e1457244
              | exact resolve b24e1457244 b24e729964
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e729964 b24e1457244
            have b24e1457427 : (σ y) = (σ (M.op y x)) := by grind
            clear b24e1457426
            have b24e1457458 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b24e121156
                 have i₂ := b24e1457427
                 grind)
              | exact superpose b24e1457427 b24e121156
              | exact resolve b24e121156 b24e1457427
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e121156
            have b24e1457623 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e1457458
                 have i₂ := b24e260
                 grind)
              | exact superpose b24e260 b24e1457458
              | exact resolve b24e1457458 b24e260
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e260 b24e1457458
            have b24e1457661 : (M.op (σ x) (σ x)) = (σ (M.op y x)) := by
              first
              | (have i₁ := b24e1457623
                 have i₂ := b24e213479
                 grind)
              | exact superpose b24e213479 b24e1457623
              | exact resolve b24e1457623 b24e213479
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e213479 b24e1457623
            have b24e1457682 : (σ y) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b24e1457661
                 have i₂ := b24e1457427
                 grind)
              | exact superpose b24e1457427 b24e1457661
              | exact resolve b24e1457661 b24e1457427
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1457427 b24e1457661
            have b24e1457696 : False := by grind
            exact b24e1457696
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b25e27 : y ≠ (M.op y y) := by grind
              have b25e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : False := by grind
              exact b25e30
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op x x) := by grind
              have b26e24 : x ≠ (M.op x y) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
                   have i₂ := b26e15 X0 X2 X1
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e39 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e15 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
                   have i₂ := b26e15 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e60 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 (τ X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e31 X0 X1
                   have i₂ := b26e20 X1 (τ X0)
                   grind)
                | exact superpose b26e20 b26e31
                | (have j1 := b26e20 X1 (τ X0)
                   grind)
                | exact resolve b26e31 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e31
              have b26e61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e68 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b26e20 b26e25
                | (have j1 := b26e20 (σ x) X0
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 (σ x) (σ y)
                   grind)
                | exact resolve b26e25 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e88 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e15 X0 X0 X0
                   have i₂ := b26e39 X0 X0
                   grind)
                | exact superpose b26e39 b26e15
                | exact resolve b26e15 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e90 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 (M.op X1 X0) X2 X3
                   have i₂ := b26e39 X1 X0
                   grind)
                | exact superpose b26e39 b26e15
                | exact resolve b26e15 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e113 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e38 X4 X2 X3 (M.op X1 X0)
                   have i₂ := b26e39 X1 X0
                   grind)
                | exact superpose b26e39 b26e38
                | exact resolve b26e38 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e125 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
                   have i₂ := b26e38 (M.op X0 X1) X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b26e38 b26e15
                | exact resolve b26e15 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e127 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
                intro X0 X3
                first
                | (have i₁ := b26e39 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
                   have i₂ := b26e38 X0 x x X3
                   grind)
                | exact superpose b26e38 b26e39
                | exact resolve b26e39 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e129 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
                intro X0 X1 X4
                first
                | (have i₁ := b26e15 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
                   have i₂ := b26e38 X1 x x X0
                   grind)
                | exact superpose b26e38 b26e15
                | exact resolve b26e15 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e132 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e125 X0 X1 X2 X3
                   have i₂ := b26e39 X0 X1
                   grind)
                | exact superpose b26e39 b26e125
                | exact resolve b26e125 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e125
              have b26e193 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b26e68 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68
              have b26e194 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b26e193
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e193 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e193
              have b26e195 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e194
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e194
                | exact resolve b26e194 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e194
              have b26e199 : ∀ X0 : G, (M.op (σ x) (M.op (σ (k x y)) (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e15 X0 (σ x) (σ y)
                   have i₂ := b26e195
                   grind)
                | exact superpose b26e195 b26e15
                | exact resolve b26e15 b26e195
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e298 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e127 (M.op X0 X1) x
                   have i₂ := b26e39 X0 X1
                   grind)
                | exact superpose b26e39 b26e127
                | exact resolve b26e127 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e309 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e15 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
                   have i₂ := b26e127 (M.op X0 X0) x
                   grind)
                | exact superpose b26e127 b26e15
                | exact resolve b26e15 b26e127
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e324 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e309 X0
                   have i₂ := b26e39 (M.op X0 X0) (M.op X0 X0)
                   grind)
                | exact superpose b26e39 b26e309
                | exact resolve b26e309 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e309
              have b26e330 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e324 X0
                   have i₂ := b26e39 X0 X0
                   grind)
                | exact superpose b26e39 b26e324
                | exact resolve b26e324 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e324
              have b26e430 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e61 x y
                   grind)
                | exact superpose b26e61 b26e22
                | (have j1 := b26e61 x y
                   grind)
                | exact resolve b26e22 b26e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e61
              have b26e517 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b26e430
                   have i₂ := b26e195
                   grind)
                | exact superpose b26e195 b26e430
                | exact resolve b26e430 b26e195
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e430
              have b26e663 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e129 (M.op X0 (M.op X0 X0)) X1 X2
                   have i₂ := b26e129 X0 X0 X0
                   grind)
                | exact superpose b26e129 b26e129
                | exact resolve b26e129 b26e129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e680 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e129 X2 X1 (M.op X0 (M.op X0 X0))
                   have i₂ := b26e129 X0 X0 X0
                   grind)
                | exact superpose b26e129 b26e129
                | exact resolve b26e129 b26e129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e705 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X0 (M.op X0 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 (M.op X0 (M.op X0 X0)) X1 X2
                   have i₂ := b26e129 X0 X0 X0
                   grind)
                | exact superpose b26e129 b26e15
                | exact resolve b26e15 b26e129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e715 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e127 (M.op x (M.op x x)) x
                   have i₂ := b26e129 x x x
                   grind)
                | exact superpose b26e129 b26e127
                | exact resolve b26e127 b26e129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e127
              have b26e1056 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op y x)) (M.op X0 X0))) = X0 ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b26e199 X0
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e199
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e199 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1061 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (M.op (σ (k x y)) X0)) := by
                intro X0
                first
                | (have i₁ := b26e199 (M.op X0 (M.op X0 X0))
                   have i₂ := b26e129 X0 X0 X0
                   grind)
                | exact superpose b26e129 b26e199
                | exact resolve b26e199 b26e129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e129
              have b26e1062 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ x) (M.op (σ (k x y)) (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e199 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
                   have i₂ := b26e38 (M.op X0 X1) X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b26e38 b26e199
                | exact resolve b26e199 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e199
              have b26e1079 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (σ x) (M.op (σ (k x y)) (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e1062 X0 X1
                   have i₂ := b26e39 X0 X1
                   grind)
                | exact superpose b26e39 b26e1062
                | exact resolve b26e1062 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1062
              have b26e1080 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op y x)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b26e1056 X0
                   grind)
                | (have r₁ := b26e1056 X0
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e1056 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1056
              have b26e1084 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op y x)) (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have j0 := b26e1080 X0
                   grind)
                | (have r₁ := b26e1080 X0
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e1080 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1080
              have b26e1175 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e705 (M.op X0 X1) X1 X0
                   have i₂ := b26e39 X0 X1
                   grind)
                | exact superpose b26e39 b26e705
                | exact resolve b26e705 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1194 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e705 X2 X0 X1
                   have i₂ := b26e705 X2 X3 X4
                   grind)
                | exact superpose b26e705 b26e705
                | exact resolve b26e705 b26e705
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1210 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e330 X2
                   have i₂ := b26e705 X2 X0 X1
                   grind)
                | exact superpose b26e705 b26e330
                | exact resolve b26e330 b26e705
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e330
              have b26e1212 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e88 X2
                   have i₂ := b26e705 X2 X0 X1
                   grind)
                | exact superpose b26e705 b26e88
                | exact resolve b26e88 b26e705
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e88
              have b26e1307 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e90 X0 (M.op X1 X0) X2 X3
                   have i₂ := b26e705 X0 X0 X1
                   grind)
                | exact superpose b26e705 b26e90
                | exact resolve b26e90 b26e705
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e705
              have b26e1317 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
                intro X0
                first
                | (have i₁ := b26e90 X0 X0 (M.op X0 X0) (M.op x x)
                   have i₂ := b26e38 X0 x x X0
                   grind)
                | exact superpose b26e38 b26e90
                | exact resolve b26e90 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1321 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e90 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
                   have i₂ := b26e90 (M.op X1 X2) X0 (M.op X1 X2) X0
                   grind)
                | exact superpose b26e90 b26e90
                | exact resolve b26e90 b26e90
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1362 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e1307 X0 X1 x x
                   have i₂ := b26e90 X0 X0 x x
                   grind)
                | exact superpose b26e90 b26e1307
                | exact resolve b26e1307 b26e90
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e90 b26e1307
              have b26e1666 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (M.op (M.op (M.op X1 (M.op X2 X0)) X0) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e1212 X0 X2 (M.op (M.op X1 (M.op X2 X0)) X0)
                   have i₂ := b26e1212 (M.op X2 X0) X1 X0
                   grind)
                | exact superpose b26e1212 b26e1212
                | exact resolve b26e1212 b26e1212
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1693 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e1666 X0 X1 X2
                   have i₂ := b26e1362 X0 (M.op X1 (M.op X2 X0))
                   grind)
                | exact superpose b26e1362 b26e1666
                | exact resolve b26e1666 b26e1362
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1666
              have b26e2813 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ x) (M.op (σ (M.op y x)) (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e1084 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
                   have i₂ := b26e38 (M.op X0 X1) X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b26e38 b26e1084
                | exact resolve b26e1084 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1084
              have b26e2852 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ (k x y)) (M.op X0 X1))) = (M.op (σ x) (M.op (σ (M.op y x)) (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e2813 X0 X1
                   have i₂ := b26e1061 (M.op X0 X1)
                   grind)
                | exact superpose b26e1061 b26e2813
                | exact resolve b26e2813 b26e1061
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2813
              have b26e2933 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
                intro X0 X1 X4 X5 X6
                first
                | (have i₁ := b26e132 (M.op (M.op x x) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0))) x x
                   have i₂ := b26e113 X0 X1 x x X4
                   grind)
                | exact superpose b26e113 b26e132
                | exact resolve b26e132 b26e113
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e113
              have b26e2957 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e132 (M.op X1 (M.op X2 X3)) (M.op X0 X0) X3 X2
                   have i₂ := b26e15 X0 (M.op X2 X3) X1
                   grind)
                | exact superpose b26e15 b26e132
                | exact resolve b26e132 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e132
              have b26e3080 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (σ x) (M.op (σ (k x y)) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e2957 X0 X1 X2 X3
                   have i₂ := b26e1079 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
                   grind)
                | exact superpose b26e1079 b26e2957
                | exact resolve b26e2957 b26e1079
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1079 b26e2957
              have b26e3098 : ∀ X0 X1 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) = (M.op X1 (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
                intro X0 X1 X4 X5 X6
                first
                | (have i₁ := b26e2933 X0 X1 X4 X5 X6
                   have i₂ := b26e1321 (M.op X4 (M.op X1 (M.op X0 X1))) X0 X1
                   grind)
                | exact superpose b26e1321 b26e2933
                | exact resolve b26e2933 b26e1321
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1321 b26e2933
              have b26e3157 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (σ x) (M.op (σ (M.op y x)) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e3080 X0 X1 X2 X3
                   have i₂ := b26e2852 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
                   grind)
                | exact superpose b26e2852 b26e3080
                | exact resolve b26e3080 b26e2852
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3080
              have b26e3163 : ∀ X0 X1 X5 X6 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
                intro X0 X1 X5 X6
                first
                | (have i₁ := b26e3098 X0 X1 x X5 X6
                   have i₂ := b26e298 X1 X0 x
                   grind)
                | exact superpose b26e298 b26e3098
                | exact resolve b26e3098 b26e298
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e298 b26e3098
              have b26e4209 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e60 (σ X0) X1
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e60
                | exact resolve b26e60 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60
              have b26e4382 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e4209 X0 X1
                   have i₂ := b26e21 X1 X0
                   grind)
                | exact superpose b26e21 b26e4209
                | (have j0 := b26e4209 X0 X1
                   grind)
                | exact resolve b26e4209 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4209
              have b26e9479 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b26e517
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e517
                | (have j1 := b26e20 y x
                   grind)
                | exact resolve b26e517 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e517
              have b26e9488 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
              clear b26e9479
              have b26e10675 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) X0) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e680 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) X2 (M.op X3 X1)
                   have i₂ := b26e663 X1 X3 X0
                   grind)
                | exact superpose b26e663 b26e680
                | exact resolve b26e680 b26e663
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e663
              have b26e11114 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e10675 X0 X1 X2 X3
                   have i₂ := b26e39 X3 X1
                   grind)
                | exact superpose b26e39 b26e10675
                | exact resolve b26e10675 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e10675
              have b26e11245 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (σ (k x y)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e11114 X0 X1 X2 X3
                   have i₂ := b26e1061 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0))
                   grind)
                | exact superpose b26e1061 b26e11114
                | exact resolve b26e11114 b26e1061
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1061 b26e11114
              have b26e11308 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) = (M.op (σ x) (M.op (σ (M.op y x)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e11245 X0 X1 X2 X3
                   have i₂ := b26e2852 (M.op X1 (M.op X1 X1)) (M.op X0 X0)
                   grind)
                | exact superpose b26e2852 b26e11245
                | exact resolve b26e11245 b26e2852
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2852 b26e11245
              have b26e11337 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e11308 X0 X1 X2 X3
                   have i₂ := b26e3157 X0 X1 X1 X1
                   grind)
                | exact superpose b26e3157 b26e11308
                | exact resolve b26e11308 b26e3157
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3157 b26e11308
              have b26e11976 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X3 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) X2) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e11337 X2 (M.op X1 X0) X3 (M.op x (M.op X1 X1))
                   have i₂ := b26e680 X0 x X1
                   grind)
                | exact superpose b26e680 b26e11337
                | exact resolve b26e11337 b26e680
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e12115 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X1 (M.op X0 (M.op X2 X0)) x
                   have i₂ := b26e11337 (M.op X1 X1) X0 x X2
                   grind)
                | exact superpose b26e11337 b26e15
                | exact resolve b26e15 b26e11337
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11337
              have b26e12410 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X3 X0) X2) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e11976 X0 X1 X2 X3
                   have i₂ := b26e715 X0 X1
                   grind)
                | exact superpose b26e715 b26e11976
                | exact resolve b26e11976 b26e715
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11976
              have b26e14383 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e12410 (M.op X2 (M.op X0 X0)) X1 X3 (M.op (M.op x x) (M.op X2 X2))
                   have i₂ := b26e38 X2 x x X0
                   grind)
                | exact superpose b26e38 b26e12410
                | exact resolve b26e12410 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38
              have b26e14398 : ∀ X0 X1 : G, (M.op (σ (k x y)) X1) = (M.op (M.op X0 (σ x)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e12410 (σ x) X0 X1 (σ y)
                   have i₂ := b26e195
                   grind)
                | exact superpose b26e195 b26e12410
                | exact resolve b26e12410 b26e195
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e18681 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) (M.op (M.op X2 X1) X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e1210 (M.op X2 X1) X1 (M.op X1 (M.op X0 X0))
                   have i₂ := b26e12115 X1 X0 X2
                   grind)
                | exact superpose b26e12115 b26e1210
                | exact resolve b26e1210 b26e12115
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1210 b26e12115
              have b26e18861 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18681 X0 X1 X2
                   have i₂ := b26e14383 X0 (M.op X1 (M.op X0 X0)) X1 (M.op (M.op X2 X1) X0)
                   grind)
                | exact superpose b26e14383 b26e18681
                | exact resolve b26e18681 b26e14383
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e14383 b26e18681
              have b26e23508 : ∀ X0 X1 : G, (M.op (σ (M.op y x)) X0) = (M.op (M.op X1 (σ x)) X0) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                intro X0 X1
                first
                | (have i₁ := b26e14398 X1 X0
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e14398
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e14398 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e14398
              have b26e24247 : ∀ X0 X1 : G, (M.op (σ (M.op y x)) X0) = (M.op (M.op X1 (σ x)) X0) ∨ x = (M.op x y) := by
                intro X0 X1
                first
                | (have j0 := b26e23508 X0 X1
                   grind)
                | (have r₁ := b26e23508 X0 X1
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e23508 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e23508
              have b26e24331 : ∀ X0 X1 : G, (M.op (σ (M.op y x)) X0) = (M.op (M.op X1 (σ x)) X0) := by
                intro X0 X1
                first
                | (have j0 := b26e24247 X0 X1
                   grind)
                | (have r₁ := b26e24247 X0 X1
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e24247 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e24247
              have b26e27547 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e18861 (M.op X1 X0) (M.op X1 X1) x
                   have i₂ := b26e680 X0 x X1
                   grind)
                | exact superpose b26e680 b26e18861
                | exact resolve b26e18861 b26e680
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e680
              have b26e28017 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e27547 X0 X1
                   have i₂ := b26e39 X1 X0
                   grind)
                | exact superpose b26e39 b26e27547
                | exact resolve b26e27547 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e27547
              have b26e28116 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e28017 X0 X1
                   have i₂ := b26e715 X0 X1
                   grind)
                | exact superpose b26e715 b26e28017
                | exact resolve b26e28017 b26e715
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e715 b26e28017
              have b26e28986 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e12410 X2 X1 (M.op X0 (M.op X2 X0)) X2
                   have i₂ := b26e28116 X0 X2
                   grind)
                | exact superpose b26e28116 b26e12410
                | exact resolve b26e12410 b26e28116
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e12410
              have b26e28987 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e18861 (M.op X0 (M.op X1 X0)) X1 X1
                   have i₂ := b26e28116 X0 X1
                   grind)
                | exact superpose b26e28116 b26e18861
                | exact resolve b26e18861 b26e28116
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e18861 b26e28116
              have b26e29144 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e28987 X0 X1
                   have i₂ := b26e39 X0 (M.op X1 X0)
                   grind)
                | exact superpose b26e39 b26e28987
                | exact resolve b26e28987 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e39 b26e28987
              have b26e29257 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e29144 X0 X1
                   have i₂ := b26e1175 X0 X1
                   grind)
                | exact superpose b26e1175 b26e29144
                | exact resolve b26e29144 b26e1175
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1175 b26e29144
              have b26e29297 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e29257 X0 X1
                   have i₂ := b26e1693 X0 X0 X1
                   grind)
                | exact superpose b26e1693 b26e29257
                | exact resolve b26e29257 b26e1693
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1693 b26e29257
              have b26e30358 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ (k x y)))) := by
                intro X0
                first
                | (have i₁ := b26e28986 (σ x) X0 (σ y)
                   have i₂ := b26e195
                   grind)
                | exact superpose b26e195 b26e28986
                | exact resolve b26e28986 b26e195
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e35791 : ∀ X0 : G, (M.op (σ (M.op y x)) (M.op X0 (M.op (σ x) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e28986 X0 x (σ x)
                   have i₂ := b26e24331 (M.op X0 (M.op (σ x) X0)) x
                   grind)
                | exact superpose b26e24331 b26e28986
                | exact resolve b26e28986 b26e24331
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e24331 b26e28986
              have b26e185010 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e29297 X3 X2
                   have i₂ := b26e3163 X2 X3 X0 X1
                   grind)
                | exact superpose b26e3163 b26e29297
                | exact resolve b26e29297 b26e3163
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29297
              have b26e185200 : ∀ X0 X1 : G, (σ (M.op y x)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ x) (σ (M.op y x))))) := by
                intro X0 X1
                first
                | (have i₁ := b26e35791 (σ (M.op y x))
                   have i₂ := b26e3163 (σ x) (σ (M.op y x)) X0 X1
                   grind)
                | exact superpose b26e3163 b26e35791
                | exact resolve b26e35791 b26e3163
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3163 b26e35791
              have b26e197404 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ (M.op y x)))) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b26e30358 X0
                   have i₂ := b26e4382 y x
                   grind)
                | exact superpose b26e4382 b26e30358
                | (have j1 := b26e4382 y x
                   grind)
                | exact resolve b26e30358 b26e4382
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4382 b26e30358
              have b26e197636 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ (M.op y x)))) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b26e197404 X0
                   grind)
                | (have r₁ := b26e197404 X0
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e197404 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e197404
              have b26e197675 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ (M.op y x)))) := by
                intro X0
                first
                | (have j0 := b26e197636 X0
                   grind)
                | (have r₁ := b26e197636 X0
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e197636 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e197636
              have b26e201675 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ x) (σ (M.op y x))))) := by
                intro X0 X1
                first
                | (have i₁ := b26e1194 X0 X1 (M.op (σ x) (σ (M.op y x))) (σ y) x
                   have i₂ := b26e197675 x
                   grind)
                | exact superpose b26e197675 b26e1194
                | exact resolve b26e1194 b26e197675
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1194 b26e197675
              have b26e201875 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
                first
                | (have i₁ := b26e201675 x x
                   have i₂ := b26e185200 x x
                   grind)
                | exact superpose b26e185200 b26e201675
                | exact resolve b26e201675 b26e185200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e185200 b26e201675
              have b26e202009 : (σ (k x y)) = (σ (M.op y x)) := by
                first
                | (have i₁ := b26e195
                   have i₂ := b26e201875
                   grind)
                | exact superpose b26e201875 b26e195
                | exact resolve b26e195 b26e201875
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e195 b26e201875
              have b26e284009 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b26e1317 (σ y)
                   have i₂ := b26e9488
                   grind)
                | exact superpose b26e9488 b26e1317
                | exact resolve b26e1317 b26e9488
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1317 b26e9488
              have b26e284010 : (σ y) = (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b26e284009
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e284009 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e284009
              have b26e284013 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b26e284010
                   have i₂ := b26e202009
                   grind)
                | exact superpose b26e202009 b26e284010
                | exact resolve b26e284010 b26e202009
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e202009 b26e284010
              have b26e302866 : (M.op y x) = (τ (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b26e16 (M.op y x)
                   have i₂ := b26e284013
                   grind)
                | exact superpose b26e284013 b26e16
                | exact resolve b26e16 b26e284013
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e284013
              have b26e302879 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b26e302866
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e302866
                | exact resolve b26e302866 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e302866
              have b26e302880 : y = (M.op y x) ∨ x = (M.op y y) := by grind
              clear b26e302879
              have b26e303183 : ∀ X0 X1 : G, (M.op x x) = (M.op y (M.op X0 (M.op (M.op X1 X0) y))) ∨ x = (M.op y y) := by
                intro X0 X1
                first
                | (have i₁ := b26e185010 X0 X1 y x
                   have i₂ := b26e302880
                   grind)
                | exact superpose b26e302880 b26e185010
                | exact resolve b26e185010 b26e302880
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e185010 b26e302880
              have b26e303198 : y = (M.op x x) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b26e303183 x x
                   have i₂ := b26e1212 x x y
                   grind)
                | exact superpose b26e1212 b26e303183
                | exact resolve b26e303183 b26e1212
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1212 b26e303183
              have b26e303296 : x = (M.op y y) := by
                first
                | (have r₁ := b26e303198
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e303198 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e303198
              have b26e303630 : x = (M.op x y) := by
                first
                | (have i₁ := b26e1362 y y
                   have i₂ := b26e303296
                   grind)
                | exact superpose b26e303296 b26e1362
                | exact resolve b26e1362 b26e303296
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1362 b26e303296
              have b26e303942 : False := by grind
              exact b26e303942
